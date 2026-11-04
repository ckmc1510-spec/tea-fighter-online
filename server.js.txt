'use strict';

// Minimal RFC 6455 WebSocket transport implemented with Node built-ins only.
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { EventEmitter } = require('node:events');

const PORT = Number(process.env.PORT || 3000);
const HOST = process.env.HOST || '0.0.0.0';
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_ROOMS = Number(process.env.MAX_ROOMS || 500);
const MAX_PAYLOAD = 180 * 1024;
const DISCONNECT_GRACE_MS = 30_000;
const INPUT_CODES = new Set(['KeyA','KeyD','KeyJ','KeyK','KeyL','KeyS','KeyU','KeyI','KeyO']);
const HP_VALUES = new Set([100,200,300,400,500,600,800,1000]);
const ROUND_VALUES = new Set([1,3,5,7,9]);
const CHARACTERS = new Set(['energy','speed','strength','time','florentino']);
const rooms = new Map();
const socketMeta = new WeakMap();

function makeFrame(opcode, payload = Buffer.alloc(0)) {
  const data = Buffer.isBuffer(payload) ? payload : Buffer.from(payload);
  let header;
  if (data.length < 126) {
    header = Buffer.from([0x80 | opcode, data.length]);
  } else if (data.length <= 0xffff) {
    header = Buffer.alloc(4); header[0] = 0x80 | opcode; header[1] = 126; header.writeUInt16BE(data.length, 2);
  } else {
    header = Buffer.alloc(10); header[0] = 0x80 | opcode; header[1] = 127; header.writeBigUInt64BE(BigInt(data.length), 2);
  }
  return Buffer.concat([header, data]);
}

class WebSocketConnection extends EventEmitter {
  constructor(socket, head, maxPayload) {
    super();
    this.socket = socket;
    this.maxPayload = maxPayload;
    this.readyState = WebSocketConnection.OPEN;
    this.buffer = Buffer.alloc(0);
    this.fragmentOpcode = 0;
    this.fragments = [];
    this.fragmentBytes = 0;
    this.isAlive = true;
    socket.on('data', chunk => this.consume(chunk));
    socket.on('error', err => this.emit('error', err));
    socket.on('close', () => { if (this.readyState !== WebSocketConnection.CLOSED) { this.readyState = WebSocketConnection.CLOSED; this.emit('close'); } });
    socket.on('end', () => { if (this.readyState !== WebSocketConnection.CLOSED) { this.readyState = WebSocketConnection.CLOSED; this.emit('close'); } });
    if (head && head.length) this.consume(head);
  }
  send(data) {
    if (this.readyState !== WebSocketConnection.OPEN) return;
    this.socket.write(makeFrame(0x1, Buffer.from(String(data))));
  }
  ping() {
    if (this.readyState === WebSocketConnection.OPEN) this.socket.write(makeFrame(0x9));
  }
  close(code = 1000, reason = '') {
    if (this.readyState !== WebSocketConnection.OPEN) return;
    this.readyState = WebSocketConnection.CLOSING;
    const text = Buffer.from(String(reason).slice(0, 100));
    const payload = Buffer.alloc(2 + text.length); payload.writeUInt16BE(code, 0); text.copy(payload, 2);
    try { this.socket.write(makeFrame(0x8, payload)); } catch (_) {}
    this.socket.end();
  }
  terminate() {
    if (this.readyState === WebSocketConnection.CLOSED) return;
    this.readyState = WebSocketConnection.CLOSED;
    this.socket.destroy();
    this.emit('close');
  }
  protocolError(code, message) { this.close(code, message); }
  consume(chunk) {
    if (this.readyState === WebSocketConnection.CLOSED) return;
    this.buffer = Buffer.concat([this.buffer, chunk]);
    while (this.buffer.length >= 2) {
      const b0 = this.buffer[0], b1 = this.buffer[1];
      const fin = (b0 & 0x80) !== 0;
      const opcode = b0 & 0x0f;
      const masked = (b1 & 0x80) !== 0;
      let length = b1 & 0x7f;
      let offset = 2;
      if (!masked) return this.protocolError(1002, 'Client frames must be masked');
      if (length === 126) {
        if (this.buffer.length < 4) return;
        length = this.buffer.readUInt16BE(2); offset = 4;
      } else if (length === 127) {
        if (this.buffer.length < 10) return;
        const big = this.buffer.readBigUInt64BE(2);
        if (big > BigInt(this.maxPayload)) return this.protocolError(1009, 'Frame too large');
        length = Number(big); offset = 10;
      }
      if (length > this.maxPayload) return this.protocolError(1009, 'Frame too large');
      if (this.buffer.length < offset + 4 + length) return;
      const mask = this.buffer.subarray(offset, offset + 4); offset += 4;
      const payload = Buffer.from(this.buffer.subarray(offset, offset + length));
      this.buffer = this.buffer.subarray(offset + length);
      for (let i = 0; i < payload.length; i++) payload[i] ^= mask[i & 3];

      if (opcode === 0x8) {
        if (this.readyState === WebSocketConnection.OPEN) {
          this.readyState = WebSocketConnection.CLOSING;
          this.socket.write(makeFrame(0x8, payload));
          this.socket.end();
        }
        return;
      }
      if (opcode === 0x9) { this.socket.write(makeFrame(0xA, payload)); continue; }
      if (opcode === 0xA) { this.isAlive = true; this.emit('pong'); continue; }
      if (opcode === 0x1 || opcode === 0x2) {
        if (this.fragmentOpcode) return this.protocolError(1002, 'Nested fragmented message');
        if (fin) {
          if (opcode !== 0x1) return this.protocolError(1003, 'Text messages only');
          this.emit('message', payload);
        } else {
          this.fragmentOpcode = opcode; this.fragments = [payload]; this.fragmentBytes = payload.length;
        }
        continue;
      }
      if (opcode === 0x0) {
        if (!this.fragmentOpcode) return this.protocolError(1002, 'Unexpected continuation');
        this.fragments.push(payload); this.fragmentBytes += payload.length;
        if (this.fragmentBytes > this.maxPayload) return this.protocolError(1009, 'Message too large');
        if (fin) {
          const message = Buffer.concat(this.fragments, this.fragmentBytes);
          const oldOpcode = this.fragmentOpcode;
          this.fragments = []; this.fragmentBytes = 0; this.fragmentOpcode = 0;
          if (oldOpcode !== 0x1) return this.protocolError(1003, 'Text messages only');
          this.emit('message', message);
        }
        continue;
      }
      return this.protocolError(1002, 'Unsupported opcode');
    }
  }
}
WebSocketConnection.OPEN = 1;
WebSocketConnection.CLOSING = 2;
WebSocketConnection.CLOSED = 3;

class WebSocketServer extends EventEmitter {
  constructor({ server, path: wsPath, maxPayload }) {
    super(); this.clients = new Set(); this.wsPath = wsPath; this.maxPayload = maxPayload;
    server.on('upgrade', (req, socket, head) => this.upgrade(req, socket, head));
  }
  upgrade(req, socket, head) {
    let url;
    try { url = new URL(req.url, `http://${req.headers.host || 'localhost'}`); } catch (_) { socket.destroy(); return; }
    if (url.pathname !== this.wsPath || req.headers.upgrade?.toLowerCase() !== 'websocket' || !req.headers['sec-websocket-key']) {
      socket.write('HTTP/1.1 404 Not Found\r\nConnection: close\r\n\r\n'); socket.destroy(); return;
    }
    const origin = req.headers.origin;
    if (origin) {
      try {
        const originHost = new URL(origin).host;
        if (originHost !== req.headers.host) { socket.write('HTTP/1.1 403 Forbidden\r\nConnection: close\r\n\r\n'); socket.destroy(); return; }
      } catch (_) { socket.destroy(); return; }
    }
    const accept = crypto.createHash('sha1').update(req.headers['sec-websocket-key'] + '258EAFA5-E914-47DA-95CA-C5AB0DC85B11').digest('base64');
    socket.write('HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Accept: ' + accept + '\r\n\r\n');
    const ws = new WebSocketConnection(socket, head, this.maxPayload);
    this.clients.add(ws);
    ws.on('close', () => this.clients.delete(ws));
    this.emit('connection', ws, req);
  }
}

function send(ws, message) {
  if (ws && ws.readyState === WebSocketConnection.OPEN) ws.send(JSON.stringify(message));
}
function code6() {
  const alphabet = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
  let code = '';
  for (let i = 0; i < 6; i++) code += alphabet[crypto.randomInt(alphabet.length)];
  return code;
}
function token() { return crypto.randomBytes(24).toString('base64url'); }
function safeLobby(input = {}) {
  const hp = Number(input.hp), rounds = Number(input.rounds);
  return {
    player1Char: CHARACTERS.has(input.player1Char) ? input.player1Char : 'energy',
    hp: HP_VALUES.has(hp) ? hp : 300,
    rounds: ROUND_VALUES.has(rounds) ? rounds : 5
  };
}
function bind(ws, room, role) {
  const slot = role === 'host' ? room.host : room.guest;
  slot.ws = ws; slot.connected = true;
  socketMeta.set(ws, { code: room.code, role });
}
function closeRoom(room, reason) {
  if (!room || !rooms.has(room.code)) return;
  rooms.delete(room.code);
  if (room.graceTimer) clearTimeout(room.graceTimer);
  send(room.host?.ws, { type:'room_closed', reason:reason || 'Phòng đã đóng.' });
  send(room.guest?.ws, { type:'room_closed', reason:reason || 'Phòng đã đóng.' });
  for (const slot of [room.host, room.guest]) if (slot?.ws && slot.ws.readyState === WebSocketConnection.OPEN) slot.ws.close(1000,'room closed');
}
function markDisconnected(room, role) {
  const slot = role === 'host' ? room.host : room.guest;
  if (!slot) return;
  slot.ws = null; slot.connected = false;
  const other = role === 'host' ? room.guest : room.host;
  send(other?.ws, { type:'peer_disconnected', role });
  if (room.graceTimer) clearTimeout(room.graceTimer);
  room.graceTimer = setTimeout(() => {
    if (!rooms.has(room.code)) return;
    if (!room.host.connected || (room.guest && !room.guest.connected)) closeRoom(room,'Thời gian kết nối lại đã hết. Phòng đã đóng.');
  }, DISCONNECT_GRACE_MS);
}
function getRoomFromSocket(ws) {
  const meta = socketMeta.get(ws); if (!meta) return null;
  const room = rooms.get(meta.code); return room ? { room, role:meta.role } : null;
}

const server = http.createServer((req,res) => {
  let url; try { url = new URL(req.url, `http://${req.headers.host || 'localhost'}`); } catch (_) { res.writeHead(400); res.end('Bad URL'); return; }
  if (url.pathname === '/healthz') {
    res.writeHead(200, {'content-type':'application/json; charset=utf-8','cache-control':'no-store'});
    res.end(JSON.stringify({ok:true,service:'tea-fighter-online',rooms:rooms.size})); return;
  }
  let requestPath; try { requestPath=decodeURIComponent(url.pathname); } catch (_) { res.writeHead(400); res.end('Bad path'); return; }
  if (requestPath === '/') requestPath='/index.html';
  const resolved=path.resolve(PUBLIC_DIR,'.'+requestPath);
  if (!resolved.startsWith(PUBLIC_DIR + path.sep) && resolved !== path.join(PUBLIC_DIR,'index.html')) { res.writeHead(403); res.end('Forbidden'); return; }
  fs.stat(resolved,(err,stat)=>{
    if(err || !stat.isFile()) {res.writeHead(404);res.end('Not found');return;}
    const ext=path.extname(resolved).toLowerCase();
    const types={'.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.json':'application/json; charset=utf-8','.png':'image/png','.svg':'image/svg+xml'};
    res.writeHead(200,{'content-type':types[ext]||'application/octet-stream','cache-control':ext==='.html'?'no-cache':'public, max-age=3600','x-content-type-options':'nosniff','referrer-policy':'strict-origin-when-cross-origin'});
    fs.createReadStream(resolved).pipe(res);
  });
});

const wss = new WebSocketServer({server,path:'/ws',maxPayload:MAX_PAYLOAD});
wss.on('connection', ws => {
  ws.isAlive=true;
  ws.on('pong',()=>{ws.isAlive=true;});
  ws.on('message',raw=>{
    let msg; try {msg=JSON.parse(raw.toString());} catch {send(ws,{type:'error',message:'Dữ liệu mạng không hợp lệ.'});return;}
    if(!msg || typeof msg.type!=='string') return;
    if(msg.type==='create_room') {
      if(socketMeta.has(ws)) return send(ws,{type:'error',message:'Kết nối này đã tham gia một phòng.'});
      if(rooms.size>=MAX_ROOMS) return send(ws,{type:'error',message:'Máy chủ đã đạt giới hạn phòng.'});
      let code; do{code=code6();}while(rooms.has(code));
      const room={code,started:false,host:{ws:null,token:token(),connected:true},guest:null,lobby:safeLobby(msg.lobby),guestCharacter:'energy',guestReady:false,graceTimer:null,inputWindowStart:Date.now(),inputCount:0,lastSnapshotAt:0};
      rooms.set(code,room);bind(ws,room,'host');send(ws,{type:'room_created',code,token:room.host.token,role:'host'});return;
    }
    if(msg.type==='join_room') {
      if(socketMeta.has(ws)) return send(ws,{type:'error',message:'Kết nối này đã tham gia một phòng.'});
      const code=String(msg.code||'').toUpperCase(),room=rooms.get(code);
      if(!room) return send(ws,{type:'error',message:'Không tìm thấy phòng. Kiểm tra lại mã phòng.'});
      if(room.started) return send(ws,{type:'error',message:'Trận đấu của phòng này đã bắt đầu.'});
      if(room.guest) return send(ws,{type:'error',message:'Phòng đã đủ hai người hoặc đang chờ người cũ kết nối lại.'});
      room.guest={ws:null,token:token(),connected:true};bind(ws,room,'guest');
      send(ws,{type:'room_joined',code,token:room.guest.token,role:'guest',lobby:room.lobby});
      send(room.host.ws,{type:'peer_joined',character:room.guestCharacter});send(ws,{type:'host_lobby',lobby:room.lobby});return;
    }
    if(msg.type==='resume') {
      const code=String(msg.code||'').toUpperCase(),room=rooms.get(code),role=msg.role==='host'?'host':'guest';
      const slot=room&&(role==='host'?room.host:room.guest);
      if(!room||!slot||slot.connected||!slot.token||slot.token!==msg.token) return send(ws,{type:'error',message:'Không thể khôi phục phiên phòng này.'});
      if(room.graceTimer){clearTimeout(room.graceTimer);room.graceTimer=null;}
      bind(ws,room,role);send(ws,{type:'resumed',code,role,lobby:room.lobby,started:room.started});
      send(role==='host'?room.guest?.ws:room.host.ws,{type:'peer_reconnected',role});if(role==='guest')send(ws,{type:'host_lobby',lobby:room.lobby});
      if (!room.host.connected || (room.guest && !room.guest.connected)) {
        room.graceTimer=setTimeout(() => {
          if (!rooms.has(room.code)) return;
          if (!room.host.connected || (room.guest && !room.guest.connected)) closeRoom(room,'Thời gian kết nối lại đã hết. Phòng đã đóng.');
        }, DISCONNECT_GRACE_MS);
      }
      return;
    }
    const context=getRoomFromSocket(ws);
    if(!context){if(msg.type==='ping')return send(ws,{type:'pong',clientTime:msg.clientTime});return send(ws,{type:'error',message:'Bạn chưa ở trong phòng nào.'});}
    const {room,role}=context;
    if(msg.type==='ping')return send(ws,{type:'pong',clientTime:msg.clientTime});
    if(msg.type==='host_lobby'&&role==='host'&&!room.started){room.lobby=safeLobby(msg.lobby);send(room.guest?.ws,{type:'host_lobby',lobby:room.lobby});return;}
    if(msg.type==='guest_lobby'&&role==='guest'&&!room.started){room.guestCharacter=CHARACTERS.has(msg.character)?msg.character:'energy';room.guestReady=!!msg.ready;send(room.host.ws,{type:'guest_lobby',character:room.guestCharacter,ready:room.guestReady});return;}
    if(msg.type==='start_match'&&role==='host'&&!room.started){
      if(!room.guest||!room.guest.connected)return send(ws,{type:'error',message:'Chưa có người chơi thứ hai.'});
      if(!room.guestReady)return send(ws,{type:'error',message:'Đối thủ chưa nhấn SẴN SÀNG.'});
      room.started=true;const config={player1Char:room.lobby.player1Char,player2Char:room.guestCharacter,hp:room.lobby.hp,rounds:room.lobby.rounds};
      send(room.host.ws,{type:'match_start',config});send(room.guest.ws,{type:'match_start',config});return;
    }
    if(msg.type==='input'&&role==='guest'&&room.started){
      if(!INPUT_CODES.has(msg.code))return;const now=Date.now();
      if(now-room.inputWindowStart>=1000){room.inputWindowStart=now;room.inputCount=0;}
      if(++room.inputCount>100)return;send(room.host.ws,{type:'input',code:msg.code,down:!!msg.down});return;
    }
    if(msg.type==='snapshot'&&role==='host'&&room.started){
      const now=Date.now();if(now-room.lastSnapshotAt<20)return;room.lastSnapshotAt=now;
      if(typeof msg.state!=='object'||!msg.state||!msg.state.p1||!msg.state.p2)return;
      send(room.guest?.ws,{type:'snapshot',state:msg.state});return;
    }
    if(msg.type==='leave_room'){
      if(role==='host')closeRoom(room,'Chủ phòng đã rời phòng. Phòng đã kết thúc.');
      else if(room.started)closeRoom(room,'Người chơi đã rời phòng. Trận đấu kết thúc.');
      else{room.guest=null;room.guestReady=false;send(room.host.ws,{type:'peer_left',reason:'Người chơi thứ hai đã rời phòng.'});socketMeta.delete(ws);return;}
      socketMeta.delete(ws);return;
    }
    send(ws,{type:'error',message:'Lệnh không được hỗ trợ trong trạng thái phòng hiện tại.'});
  });
  ws.on('close',()=>{const context=getRoomFromSocket(ws);if(!context)return;const {room,role}=context;const slot=role==='host'?room.host:room.guest;if(slot&&slot.ws===ws)markDisconnected(room,role);socketMeta.delete(ws);});
  ws.on('error',()=>{});
});

const heartbeat=setInterval(()=>{for(const ws of wss.clients){if(ws.isAlive===false){ws.terminate();continue;}ws.isAlive=false;ws.ping();}},25_000);
server.on('close',()=>clearInterval(heartbeat));
server.listen(PORT,HOST,()=>{console.log(`Tea Fighter Online running at http://${HOST}:${PORT}`);console.log(`WebSocket relay: ws://<host>:${PORT}/ws`);});
