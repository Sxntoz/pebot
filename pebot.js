#!/usr/bin/env node
"use strict";

const dgram = require("dgram");
const dns = require("dns").promises;
const crypto = require("crypto");
const fs = require("fs");
const zlib = require("zlib");
const { EventEmitter } = require("events");

const RAKNET_PROTOCOL = 6;
const MCPE_PROTOCOL = 84;
const MAGIC = Buffer.from("00ffff00fefefefefdfdfdfd12345678", "hex");

const ID = {
  UNCONNECTED_PING: 0x01,
  UNCONNECTED_PONG: 0x1c,
  OPEN_CONNECTION_REQUEST_1: 0x05,
  OPEN_CONNECTION_REPLY_1: 0x06,
  OPEN_CONNECTION_REQUEST_2: 0x07,
  OPEN_CONNECTION_REPLY_2: 0x08,
  CLIENT_CONNECT: 0x09,
  SERVER_HANDSHAKE: 0x10,
  CLIENT_HANDSHAKE: 0x13,
  ACK: 0xc0,
  DATA_MIN: 0x80,
  DATA_MAX: 0x8f,
};

const MCPE = {
  LOGIN: 0x01,
  PLAY_STATUS: 0x02,
  DISCONNECT: 0x05,
  BATCH: 0x06,
  TEXT: 0x07,
  START_GAME: 0x09,
  REQUEST_CHUNK_RADIUS: 0x3d,
};

function writeTriadLE(value) {
  const b = Buffer.alloc(3);
  b[0] = value & 0xff;
  b[1] = (value >>> 8) & 0xff;
  b[2] = (value >>> 16) & 0xff;
  return b;
}

function readTriadLE(buffer, offset) {
  return buffer[offset] | (buffer[offset + 1] << 8) | (buffer[offset + 2] << 16);
}

function writeShortBE(value) {
  const b = Buffer.alloc(2);
  b.writeUInt16BE(value & 0xffff, 0);
  return b;
}

function writeIntBE(value) {
  const b = Buffer.alloc(4);
  b.writeInt32BE(value | 0, 0);
  return b;
}

function writeIntLE(value) {
  const b = Buffer.alloc(4);
  b.writeInt32LE(value | 0, 0);
  return b;
}

function writeLongBE(value) {
  const b = Buffer.alloc(8);
  b.writeBigInt64BE(BigInt(value), 0);
  return b;
}

function readLongBE(buffer, offset) {
  return buffer.readBigInt64BE(offset);
}

function writeAddress(address, port) {
  const parts = address.split(".").map((part) => Number(part));
  if (parts.length !== 4 || parts.some((part) => !Number.isInteger(part) || part < 0 || part > 255)) {
    throw new Error(`Only IPv4 addresses are supported, got ${address}`);
  }

  return Buffer.from([
    0x04,
    (~parts[0]) & 0xff,
    (~parts[1]) & 0xff,
    (~parts[2]) & 0xff,
    (~parts[3]) & 0xff,
    (port >>> 8) & 0xff,
    port & 0xff,
  ]);
}

function readAddress(buffer, offset) {
  const version = buffer[offset++];
  if (version !== 4) {
    throw new Error(`Unsupported RakNet address version ${version}`);
  }

  const address = [
    (~buffer[offset++]) & 0xff,
    (~buffer[offset++]) & 0xff,
    (~buffer[offset++]) & 0xff,
    (~buffer[offset++]) & 0xff,
  ].join(".");
  const port = buffer.readUInt16BE(offset);
  return { address, port, offset: offset + 2 };
}

function writeString(value) {
  const body = Buffer.from(String(value), "utf8");
  return Buffer.concat([writeShortBE(body.length), body]);
}

function readString(buffer, offset) {
  const length = buffer.readUInt16BE(offset);
  const start = offset + 2;
  return { value: buffer.subarray(start, start + length).toString("utf8"), offset: start + length };
}

function base64urlJSON(value) {
  return Buffer.from(JSON.stringify(value)).toString("base64url");
}

function unsignedJWT(payload) {
  return `${base64urlJSON({ alg: "none", typ: "JWT" })}.${base64urlJSON(payload)}.`;
}

function uuidV4() {
  if (crypto.randomUUID) return crypto.randomUUID();
  const b = crypto.randomBytes(16);
  b[6] = (b[6] & 0x0f) | 0x40;
  b[8] = (b[8] & 0x3f) | 0x80;
  const h = b.toString("hex");
  return `${h.slice(0, 8)}-${h.slice(8, 12)}-${h.slice(12, 16)}-${h.slice(16, 20)}-${h.slice(20)}`;
}

function randomLong() {
  return crypto.randomBytes(8).readBigInt64BE(0);
}

function encodeEncapsulated(payload, state) {
  const reliability = 3; // RELIABLE_ORDERED
  const bitLength = payload.length << 3;
  const messageIndex = state.messageIndex++;
  const orderIndex = state.orderIndex++;

  return Buffer.concat([
    Buffer.from([reliability << 5]),
    writeShortBE(bitLength),
    writeTriadLE(messageIndex),
    writeTriadLE(orderIndex),
    Buffer.from([0x00]),
    payload,
  ]);
}

function decodeEncapsulated(buffer, offset) {
  const flags = buffer[offset++];
  const reliability = (flags & 0xe0) >> 5;
  const hasSplit = (flags & 0x10) !== 0;
  const length = Math.ceil(buffer.readUInt16BE(offset) / 8);
  offset += 2;

  if (reliability > 0) {
    if (reliability >= 2 && reliability !== 5) offset += 3;
    if (reliability <= 4 && reliability !== 2) offset += 4;
  }

  if (hasSplit) offset += 10;
  let split = null;
  if (hasSplit) {
    const splitOffset = offset - 10;
    split = {
      count: buffer.readInt32BE(splitOffset),
      id: buffer.readUInt16BE(splitOffset + 4),
      index: buffer.readInt32BE(splitOffset + 6),
    };
  }

  const payload = buffer.subarray(offset, offset + length);
  return { payload, offset: offset + length, split };
}

function encodeDataPacket(encapsulated, state) {
  const id = ID.DATA_MIN + (state.sequenceNumber & 0x0f);
  const seq = state.sequenceNumber++;
  return Buffer.concat([Buffer.from([id]), writeTriadLE(seq), encapsulated]);
}

function encodeAck(seq) {
  return Buffer.concat([
    Buffer.from([ID.ACK]),
    writeShortBE(1),
    Buffer.from([0x01]),
    writeTriadLE(seq),
  ]);
}

function encodeLogin({ username, uuid, host, port, clientId, skinData, skinId }) {
  const now = Math.floor(Date.now() / 1000);
  const chainToken = unsignedJWT({
    nbf: now - 60,
    exp: now + 86400,
    extraData: {
      displayName: username,
      identity: uuid,
    },
    identityPublicKey: "",
  });

  const skinToken = unsignedJWT({
    ClientRandomId: Number(clientId % 2147483647n),
    ServerAddress: `${host}:${port}`,
    SkinId: skinId || "pebot",
    SkinData: normalizeSkinData(skinData).toString("base64"),
  });

  const chainJson = Buffer.from(JSON.stringify({ chain: [chainToken] }), "utf8");
  const skin = Buffer.from(skinToken, "utf8");
  const compressed = zlib.deflateSync(Buffer.concat([
    writeIntLE(chainJson.length),
    chainJson,
    writeIntLE(skin.length),
    skin,
  ]));

  return Buffer.concat([
    Buffer.from([MCPE.LOGIN]),
    writeIntBE(MCPE_PROTOCOL),
    writeIntBE(compressed.length),
    compressed,
  ]);
}

function normalizeSkinData(input) {
  if (!input) return Buffer.alloc(64 * 32 * 4, 0xff);
  const skin = Buffer.isBuffer(input) ? input : Buffer.from(input, "base64");
  const validSizes = new Set([
    64 * 32 * 4,
    64 * 64 * 4,
    128 * 128 * 4,
  ]);

  if (!validSizes.has(skin.length)) {
    throw new Error(`Invalid skin size ${skin.length}. Use raw RGBA skin data: 8192, 16384 or 65536 bytes.`);
  }

  return skin;
}

function loadSkinFile(file) {
  const data = fs.readFileSync(file);
  if (data.subarray(0, 8).equals(Buffer.from("89504e470d0a1a0a", "hex"))) {
    return decodePngSkin(data);
  }
  return normalizeSkinData(data);
}

function decodePngSkin(png) {
  let offset = 8;
  let width = 0;
  let height = 0;
  let bitDepth = 0;
  let colorType = 0;
  const idat = [];

  while (offset + 12 <= png.length) {
    const length = png.readUInt32BE(offset);
    const type = png.subarray(offset + 4, offset + 8).toString("ascii");
    const data = png.subarray(offset + 8, offset + 8 + length);
    offset += 12 + length;

    if (type === "IHDR") {
      width = data.readUInt32BE(0);
      height = data.readUInt32BE(4);
      bitDepth = data[8];
      colorType = data[9];
      if (data[10] !== 0 || data[11] !== 0 || data[12] !== 0) {
        throw new Error("Unsupported PNG skin: interlaced or non-standard compression/filter.");
      }
    } else if (type === "IDAT") {
      idat.push(data);
    } else if (type === "IEND") {
      break;
    }
  }

  if (bitDepth !== 8 || ![2, 6].includes(colorType)) {
    throw new Error("Unsupported PNG skin. Use 8-bit RGB or RGBA PNG.");
  }

  const validDimensions = new Set(["64x32", "64x64", "128x128"]);
  if (!validDimensions.has(`${width}x${height}`)) {
    throw new Error(`Invalid PNG skin dimensions ${width}x${height}. Use 64x32, 64x64 or 128x128.`);
  }

  const channels = colorType === 6 ? 4 : 3;
  const stride = width * channels;
  const inflated = zlib.inflateSync(Buffer.concat(idat));
  const raw = Buffer.alloc(width * height * channels);
  let inOffset = 0;
  let outOffset = 0;
  let previous = Buffer.alloc(stride);

  for (let y = 0; y < height; y++) {
    const filter = inflated[inOffset++];
    const line = Buffer.from(inflated.subarray(inOffset, inOffset + stride));
    inOffset += stride;

    for (let x = 0; x < stride; x++) {
      const left = x >= channels ? line[x - channels] : 0;
      const up = previous[x] || 0;
      const upLeft = x >= channels ? previous[x - channels] || 0 : 0;
      if (filter === 1) line[x] = (line[x] + left) & 0xff;
      else if (filter === 2) line[x] = (line[x] + up) & 0xff;
      else if (filter === 3) line[x] = (line[x] + Math.floor((left + up) / 2)) & 0xff;
      else if (filter === 4) line[x] = (line[x] + paeth(left, up, upLeft)) & 0xff;
      else if (filter !== 0) throw new Error(`Unsupported PNG filter ${filter}.`);
    }

    line.copy(raw, outOffset);
    outOffset += stride;
    previous = line;
  }

  const rgba = Buffer.alloc(width * height * 4);
  for (let src = 0, dst = 0; src < raw.length; src += channels, dst += 4) {
    rgba[dst] = raw[src];
    rgba[dst + 1] = raw[src + 1];
    rgba[dst + 2] = raw[src + 2];
    rgba[dst + 3] = channels === 4 ? raw[src + 3] : 0xff;
  }

  return normalizeSkinData(rgba);
}

function paeth(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  if (pb <= pc) return b;
  return c;
}

function encodeText(message, source = "") {
  return Buffer.concat([
    Buffer.from([MCPE.TEXT, 0x01]),
    writeString(source),
    writeString(message),
  ]);
}

function encodeRequestChunkRadius(radius) {
  return Buffer.concat([Buffer.from([MCPE.REQUEST_CHUNK_RADIUS]), writeIntBE(radius)]);
}

function splitBatchPayload(payload) {
  const packets = [];
  let offset = 0;
  while (offset + 4 <= payload.length) {
    const length = payload.readInt32BE(offset);
    offset += 4;
    if (length <= 0 || offset + length > payload.length) break;
    packets.push(payload.subarray(offset, offset + length));
    offset += length;
  }
  return packets;
}

function parseServerName(name) {
  const parts = name.split(";");
  return {
    raw: name,
    edition: parts[0],
    motd: parts[1],
    protocol: Number(parts[2]),
    version: parts[3],
    players: Number(parts[4]),
    maxPlayers: Number(parts[5]),
  };
}

class PEBot extends EventEmitter {
  constructor(options = {}) {
    super();
    this.host = options.host || "127.0.0.1";
    this.address = options.address || null;
    this.port = Number(options.port || 19132);
    this.username = options.username || "PEBot";
    this.uuid = options.uuid || uuidV4();
    this.skinId = options.skinId || "pebot";
    this.skinData = options.skinData || null;
    this.mtu = Number(options.mtu || 1400);
    this.clientId = options.clientId !== undefined ? BigInt(options.clientId) : randomLong();
    this.serverId = 0n;
    this.connected = false;
    this.raknetReady = false;
    this.loggedIn = false;
    this._state = { sequenceNumber: 0, messageIndex: 0, orderIndex: 0 };
    this._socket = dgram.createSocket("udp4");
    this._pending = [];
    this._splits = new Map();
    this._raknetReadyPromise = new Promise((resolve) => {
      this._resolveRaknetReady = resolve;
    });
  }

  async ping() {
    await this._bind();
    const pingId = BigInt(Date.now());
    const packet = Buffer.concat([Buffer.from([ID.UNCONNECTED_PING]), writeLongBE(pingId), MAGIC]);
    this._send(packet);

    const message = await this._waitFor((msg) => msg[0] === ID.UNCONNECTED_PONG);
    const pongPing = readLongBE(message, 1);
    const serverId = readLongBE(message, 9);
    const serverName = readString(message, 33).value;
    return { pingId: pongPing, serverId, ...parseServerName(serverName) };
  }

  async connect() {
    await this._bind();
    await this._resolveHost();
    this.emit("connectStart");

    const request1 = Buffer.concat([
      Buffer.from([ID.OPEN_CONNECTION_REQUEST_1]),
      MAGIC,
      Buffer.from([RAKNET_PROTOCOL]),
      Buffer.alloc(Math.max(0, this.mtu - 18)),
    ]);

    const reply1 = await this._waitForWithRetry(
      () => this._send(request1),
      (msg) => msg[0] === ID.OPEN_CONNECTION_REPLY_1,
      "OPEN_CONNECTION_REPLY_1",
    );
    this.serverId = readLongBE(reply1, 17);
    this.mtu = reply1.readUInt16BE(26);
    this.emit("openConnection1", { serverId: this.serverId, mtu: this.mtu });

    const request2 = Buffer.concat([
      Buffer.from([ID.OPEN_CONNECTION_REQUEST_2]),
      MAGIC,
      writeAddress(this.address, this.port),
      writeShortBE(this.mtu),
      writeLongBE(this.clientId),
    ]);

    const reply2 = await this._waitForWithRetry(
      () => this._send(request2),
      (msg) => msg[0] === ID.OPEN_CONNECTION_REPLY_2,
      "OPEN_CONNECTION_REPLY_2",
    );
    this.emit("openConnection2", readAddress(reply2, 25));

    this._sendRaknetPayload(Buffer.concat([
      Buffer.from([ID.CLIENT_CONNECT]),
      writeLongBE(this.clientId),
      writeLongBE(BigInt(Date.now())),
      Buffer.from([0x00]),
    ]));

    this.connected = true;
    this.emit("connect");
    return this;
  }

  async login() {
    if (!this.connected) await this.connect();
    if (!this.raknetReady) {
      await this._raknetReadyPromise;
    }

    const login = encodeLogin({
      username: this.username,
      uuid: this.uuid,
      host: this.host,
      port: this.port,
      clientId: this.clientId,
      skinId: this.skinId,
      skinData: this.skinData,
    });

    this._sendMcpe(login);
    this.emit("loginSent", { username: this.username, protocol: MCPE_PROTOCOL });
    return this;
  }

  chat(message) {
    this._sendMcpe(encodeText(message, this.username));
  }

  requestChunkRadius(radius = 2) {
    this._sendMcpe(encodeRequestChunkRadius(radius));
  }

  close() {
    this._socket.close();
    this.connected = false;
    this.raknetReady = false;
    this.emit("end");
  }

  _sendMcpe(packet) {
    this._sendRaknetPayload(Buffer.concat([Buffer.from([0xfe]), packet]));
  }

  _sendRaknetPayload(payload) {
    this._send(encodeDataPacket(encodeEncapsulated(payload, this._state), this._state));
  }

  _send(packet) {
    this._socket.send(packet, this.port, this.address || this.host);
  }

  async _resolveHost() {
    if (this.address) return this.address;
    if (/^\d{1,3}(?:\.\d{1,3}){3}$/.test(this.host)) {
      this.address = this.host;
      return this.address;
    }

    const result = await dns.lookup(this.host, { family: 4 });
    this.address = result.address;
    this.emit("resolved", { host: this.host, address: this.address });
    return this.address;
  }

  _bind() {
    if (this._bound) return this._bound;
    this._bound = new Promise((resolve) => {
      this._socket.once("listening", resolve);
      this._socket.on("message", (msg, rinfo) => this._handleMessage(msg, rinfo));
      this._socket.on("error", (err) => this.emit("error", err));
      this._socket.bind(0);
    });
    return this._bound;
  }

  _waitFor(predicate) {
    return new Promise((resolve) => {
      this._pending.push({
        predicate,
        resolve: (msg, rinfo) => {
          resolve(msg, rinfo);
        },
      });
    });
  }

  _waitForWithRetry(sendFn, predicate, label, interval = 2000) {
    sendFn();
    this.emit("waiting", label);
    const timer = setInterval(sendFn, interval);
    return this._waitFor(predicate).finally(() => clearInterval(timer));
  }

  _handleMessage(msg, rinfo) {
    for (const entry of [...this._pending]) {
      if (entry.predicate(msg, rinfo)) {
        this._pending.splice(this._pending.indexOf(entry), 1);
        entry.resolve(msg, rinfo);
        return;
      }
    }

    const pid = msg[0];
    if (pid >= ID.DATA_MIN && pid <= ID.DATA_MAX) {
      this._handleDataPacket(msg);
      return;
    }

    this.emit("raw", msg, rinfo);
  }

  _handleDataPacket(msg) {
    const seq = readTriadLE(msg, 1);
    this._send(encodeAck(seq));

    let offset = 4;
    while (offset < msg.length) {
      const decoded = decodeEncapsulated(msg, offset);
      offset = decoded.offset;
      const payload = this._reassembleSplit(decoded);
      if (payload) this._handleRaknetPayload(payload);
    }
  }

  _reassembleSplit(packet) {
    if (!packet.split) return packet.payload;

    const { count, id, index } = packet.split;
    if (count <= 0 || count > 256 || index < 0 || index >= count) return null;

    if (!this._splits.has(id)) {
      this._splits.set(id, { count, parts: new Map(), createdAt: Date.now() });
    }

    const entry = this._splits.get(id);
    entry.parts.set(index, packet.payload);

    for (const [splitId, split] of this._splits) {
      if (Date.now() - split.createdAt > 10000) this._splits.delete(splitId);
    }

    if (entry.parts.size !== entry.count) return null;

    const buffers = [];
    for (let i = 0; i < entry.count; i++) {
      if (!entry.parts.has(i)) return null;
      buffers.push(entry.parts.get(i));
    }

    this._splits.delete(id);
    return Buffer.concat(buffers);
  }

  _handleRaknetPayload(payload) {
    const pid = payload[0];
    if (pid === ID.SERVER_HANDSHAKE) {
      this._sendClientHandshake(payload);
      this.raknetReady = true;
      this._resolveRaknetReady();
      this.emit("raknetReady");
      return;
    }

    if (pid === 0xfe) {
      this._handleMcpe(payload.subarray(1));
      return;
    }

    this.emit("raknetPacket", payload);
  }

  _sendClientHandshake(serverHandshake) {
    let observed = null;
    try {
      observed = readAddress(serverHandshake, 1);
    } catch (_) {
      // Some old RakNet servers are forgiving here. Keep the configured target.
    }

    const systemAddresses = [];
    systemAddresses.push(observed ? writeAddress(observed.address, observed.port) : writeAddress("0.0.0.0", 0));
    for (let i = 1; i < 10; i++) systemAddresses.push(writeAddress("0.0.0.0", 0));

    this._sendRaknetPayload(Buffer.concat([
      Buffer.from([ID.CLIENT_HANDSHAKE]),
      writeAddress(this.address || this.host, this.port),
      ...systemAddresses,
      writeLongBE(BigInt(Date.now())),
      writeLongBE(BigInt(Date.now())),
    ]));
  }

  _handleMcpe(packet) {
    const pid = packet[0];
    if (pid === MCPE.BATCH) {
      const length = packet.readInt32BE(1);
      const payload = zlib.inflateSync(packet.subarray(5, 5 + length));
      for (const inner of splitBatchPayload(payload)) this._handleMcpe(inner);
      return;
    }

    if (pid === MCPE.PLAY_STATUS) {
      const status = packet.readInt32BE(1);
      this.emit("playStatus", status);
      if (status === 0 && !this.loggedIn) {
        this.loggedIn = true;
        this.emit("login");
        this.requestChunkRadius(2);
      }
      return;
    }

    if (pid === MCPE.TEXT) {
      const type = packet[1];
      let offset = 2;
      let source = "";
      if (type === 1 || type === 3) {
        const sourceString = readString(packet, offset);
        source = sourceString.value;
        offset = sourceString.offset;
      }
      const messageString = readString(packet, offset);
      const message = { type, source, message: messageString.value };
      this.emit("message", message);
      if (type === 1) this.emit("chat", message);
      else if (type === 3) this.emit("popup", message);
      else if (type === 4) this.emit("tip", message);
      else if (type === 5) this.emit("system", message);
      return;
    }

    if (pid === MCPE.DISCONNECT) {
      this.emit("kicked", packet.subarray(1).toString("utf8"));
      return;
    }

    if (pid === MCPE.START_GAME) {
      this.emit("spawn");
      return;
    }

    this.emit("packet", { id: pid, buffer: packet });
  }
}

function createBot(options) {
  const bot = new PEBot(options);
  setImmediate(async () => {
    try {
      await bot.connect();
      await bot.login();
    } catch (err) {
      bot.emit("error", err);
    }
  });
  return bot;
}

module.exports = {
  createBot,
  PEBot,
  loadSkinFile,
  ping: (options) => new PEBot(options).ping(),
};

if (require.main === module) {
  const args = Object.fromEntries(process.argv.slice(2).map((arg) => {
    const [key, ...rest] = arg.replace(/^--/, "").split("=");
    return [key, rest.join("=") || true];
  }));

  const bot = createBot({
    host: args.host || "127.0.0.1",
    port: args.port || 19132,
    username: args.username || "PEBot",
    skinId: args["skin-id"] || args.skinId || "pebot",
    skinData: args.skin ? loadSkinFile(String(args.skin)) : null,
  });

  bot.on("connect", () => console.log("RakNet conectado"));
  bot.on("resolved", ({ host, address }) => console.log(`${host} -> ${address}`));
  bot.on("raknetReady", () => console.log("RakNet handshake pronto"));
  bot.on("loginSent", () => console.log("Login enviado"));
  bot.on("login", () => console.log("Login aceito"));
  bot.on("spawn", () => console.log("Spawn recebido"));
  bot.on("message", (msg) => console.log(`<${msg.source}> ${msg.message}`));
  bot.on("kicked", (reason) => console.log(`Kick: ${reason}`));
  bot.on("error", (err) => {
    console.error(err.message);
    process.exitCode = 1;
  });
}
