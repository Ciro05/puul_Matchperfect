// ============================================
// PUUL · Route Matching Algorithm
// Monterrey 2026 Hackathon
// ============================================

// ---- DATA LOADING ----
let CONDUCTORES = [];
let PASAJEROS_TESTS = [];

async function loadData() {
  try {
    const [routesRes, testsRes] = await Promise.all([
      fetch('rutas_conductores.json'),
      fetch('rutas_pasajeros.json')
    ]);
    CONDUCTORES = await routesRes.json();
    PASAJEROS_TESTS = await testsRes.json();
    // Parse waypoints
    CONDUCTORES.forEach(r => {
      if (typeof r.waypoints === 'string') {
        try { r.waypoints = JSON.parse(r.waypoints); } catch(e) { r.waypoints = []; }
      }
      r.origin_lat = parseFloat(r.origin_lat);
      r.origin_lng = parseFloat(r.origin_lng);
      r.destination_lat = parseFloat(r.destination_lat);
      r.destination_lng = parseFloat(r.destination_lng);
    });
    document.getElementById('stat-routes').textContent = CONDUCTORES.length;
    initPresets();
  } catch(e) {
    console.error('Error loading data:', e);
  }
}

// ---- MATH UTILITIES ----
const R_EARTH = 6371000; // meters

function toRad(deg) { return deg * Math.PI / 180; }

function haversine(lat1, lng1, lat2, lng2) {
  const dLat = toRad(lat2 - lat1);
  const dLng = toRad(lng2 - lng1);
  const a = Math.sin(dLat/2)**2 + Math.cos(toRad(lat1))*Math.cos(toRad(lat2))*Math.sin(dLng/2)**2;
  return R_EARTH * 2 * Math.atan2(Math.sqrt(a), Math.sqrt(1-a));
}

// Point-to-segment distance (returns meters and closest point)
function ptSegDist(px, py, ax, ay, bx, by) {
  const dx = bx - ax, dy = by - ay;
  const lenSq = dx*dx + dy*dy;
  if (lenSq === 0) return { dist: haversine(px, py, ax, ay), t: 0, cx: ax, cy: ay };
  let t = ((px-ax)*dx + (py-ay)*dy) / lenSq;
  t = Math.max(0, Math.min(1, t));
  const cx = ax + t*dx, cy = ay + t*dy;
  return { dist: haversine(px, py, cx, cy), t, cx, cy };
}

// Point-to-polyline: returns closest segment index, dist, and param t along segment
function ptPolylineDist(lat, lng, polyline) {
  let minDist = Infinity, bestIdx = 0, bestT = 0;
  for (let i = 0; i < polyline.length - 1; i++) {
    const [la, lna] = polyline[i], [lb, lnb] = polyline[i+1];
    const res = ptSegDist(lat, lng, la, lna, lb, lnb);
    if (res.dist < minDist) { minDist = res.dist; bestIdx = i; bestT = res.t; }
  }
  // Fractional index along polyline
  const fracIdx = bestIdx + bestT;
  return { dist: minDist, fracIdx };
}

// Cumulative distance along polyline up to index i+t
function polylineCumDist(polyline) {
  const cum = [0];
  for (let i = 1; i < polyline.length; i++) {
    cum.push(cum[i-1] + haversine(polyline[i-1][0], polyline[i-1][1], polyline[i][0], polyline[i][1]));
  }
  return cum;
}

function interpCumDist(cum, fracIdx) {
  const i = Math.floor(fracIdx);
  const t = fracIdx - i;
  if (i >= cum.length - 1) return cum[cum.length - 1];
  return cum[i] + t * (cum[i+1] - cum[i]);
}

// ---- BACKTRACKING DETECTION ----
// Check if pickup precedes dropoff in the driver's path direction
function checkBacktracking(pickupFrac, dropoffFrac) {
  return dropoffFrac > pickupFrac; // true = no backtracking
}

// ---- SCORING ENGINE ----
const WEIGHTS = {
  proximity: 0.25,   // avg pickup+dropoff dist to polyline
  coverage: 0.25,    // shared segment / passenger trip length
  schedule: 0.15,    // time compatibility
  detour: 0.10,      // penalize detour distance
  backtrack: 0.25    // binary - 0 if backtracking
};

const PROX_THRESHOLD = 800; // meters - beyond this score drops to 0
const MAX_DETOUR = 5000;     // meters

function scoreRoute(conductor, pickup, dropoff, desiredTimeMin, timeWindowMin) {
  const waypoints = conductor.waypoints;
  if (!waypoints || waypoints.length < 2) return null;

  // 1. Proximity
  const pickupProx = ptPolylineDist(pickup.lat, pickup.lng, waypoints);
  const dropoffProx = ptPolylineDist(dropoff.lat, dropoff.lng, waypoints);

  if (pickupProx.dist > PROX_THRESHOLD || dropoffProx.dist > PROX_THRESHOLD) return null;

  // 2. Backtracking check (CRITICAL - score = 0 if reverse)
  const forwardOrder = checkBacktracking(pickupProx.fracIdx, dropoffProx.fracIdx);
  if (!forwardOrder) return null; // Hard reject

  // 3. Coverage
  const cum = polylineCumDist(waypoints);
  const totalPolylineLen = cum[cum.length - 1];
  const pickupDistOnRoute = interpCumDist(cum, pickupProx.fracIdx);
  const dropoffDistOnRoute = interpCumDist(cum, dropoffProx.fracIdx);
  const sharedSegment = Math.max(0, dropoffDistOnRoute - pickupDistOnRoute);
  const passengerTripDist = haversine(pickup.lat, pickup.lng, dropoff.lat, dropoff.lng);
  const coverageScore = Math.min(1, sharedSegment / Math.max(passengerTripDist, 1));

  // 4. Proximity score (normalized, inverted distance)
  const avgProxDist = (pickupProx.dist + dropoffProx.dist) / 2;
  const proxScore = Math.max(0, 1 - avgProxDist / PROX_THRESHOLD);

  // 5. Schedule compatibility
  const deptMin = timeToMin(conductor.departure_time);
  let scheduleScore = 0;
  if (desiredTimeMin !== null) {
    const diff = Math.abs(deptMin - desiredTimeMin);
    if (diff <= timeWindowMin) {
      scheduleScore = 1 - (diff / timeWindowMin) * 0.5; // graduated, not binary
    } else {
      return null; // Hard filter if outside window
    }
  } else {
    scheduleScore = 1;
  }

  // 6. Detour score (how much does driver deviate from their route to pick up)
  const detourPenalty = Math.min(1, pickupProx.dist / MAX_DETOUR);
  const detourScore = 1 - detourPenalty;

  // 7. Seats available
  const seatsBonus = conductor.seats_available > 0 ? 0 : -1;
  if (seatsBonus < 0) return null;

  // FINAL SCORE
  const score = 
    proxScore * 0.25 +
    coverageScore * 0.25 +
    scheduleScore * 0.15 +
    detourScore * 0.10 +
    1.0 * 0.25; // backtracking passed = full marks

  // Add seat availability small bonus
  const seatBonus = Math.min(0.03, conductor.seats_available * 0.01);

  return {
    route_id: conductor.route_id,
    conductor,
    score: Math.min(1, score + seatBonus),
    proxScore,
    coverageScore,
    scheduleScore,
    detourScore,
    detourMeters: Math.round(pickupProx.dist),
    pickupDist: Math.round(pickupProx.dist),
    dropoffDist: Math.round(dropoffProx.dist),
    sharedKm: (sharedSegment / 1000).toFixed(2),
    passengerKm: (passengerTripDist / 1000).toFixed(2),
    coverage_pct: Math.round(coverageScore * 100),
    pickupFracIdx: pickupProx.fracIdx,
    dropoffFracIdx: dropoffProx.fracIdx,
    waypoints
  };
}

function timeToMin(t) {
  if (!t) return 0;
  const [h, m] = t.split(':').map(Number);
  return h * 60 + m;
}

// ---- MAIN SEARCH ----
function findBestRoutes(pickup, dropoff, desiredTimeStr, timeWindowMin) {
  const desiredTimeMin = desiredTimeStr ? timeToMin(desiredTimeStr) : null;
  const results = [];

  for (const conductor of CONDUCTORES) {
    const result = scoreRoute(conductor, pickup, dropoff, desiredTimeMin, timeWindowMin);
    if (result) results.push(result);
  }

  // Sort by score descending
  results.sort((a, b) => b.score - a.score);

  // Ensure minimum score gap between ranked routes (differentiation)
  const top = results.slice(0, 5);
  return top;
}

// ---- MAPS ----
let heroMap, searchMap, resultsMap;
let pickupMarker = null, dropoffMarker = null;
let pickupState = null, dropoffState = null;
let mapClickMode = null; // 'pickup' or 'dropoff'
let routePolylines = [];
let activeRouteIdx = -1;

const ROUTE_COLORS = ['#AAFF00', '#444444', '#888888', '#BBBBBB', '#DDDDDD'];
const ROUTE_COLORS_HOVER = ['#88CC00', '#222222', '#555555', '#999999', '#BBBBBB'];

function initMaps() {
  // Hero mini-map
  heroMap = L.map('hero-map', { zoomControl: false, scrollWheelZoom: false, dragging: false, touchZoom: false, doubleClickZoom: false, keyboard: false });
  L.tileLayer('https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png', { attribution: '', maxZoom: 15 }).addTo(heroMap);
  heroMap.setView([25.70, -100.32], 11);

  // Draw a few sample routes on hero map
  setTimeout(() => {
    CONDUCTORES.slice(0, 12).forEach((c, i) => {
      const color = i === 0 ? '#AAFF00' : 'rgba(100,100,100,0.25)';
      const weight = i === 0 ? 3 : 1.5;
      L.polyline(c.waypoints, { color, weight, opacity: 0.7 }).addTo(heroMap);
    });
  }, 300);

  // Search map
  searchMap = L.map('search-map', { zoomControl: true });
  L.tileLayer('https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png', { attribution: '© OpenStreetMap © CartoDB', maxZoom: 18 }).addTo(searchMap);
  searchMap.setView([25.70, -100.32], 11);

  searchMap.on('click', onSearchMapClick);

  // Results map
  resultsMap = L.map('results-map', { zoomControl: true });
  L.tileLayer('https://{s}.basemaps.cartocdn.com/light_all/{z}/{x}/{y}{r}.png', { attribution: '© OpenStreetMap © CartoDB', maxZoom: 18 }).addTo(resultsMap);
  resultsMap.setView([25.70, -100.32], 11);
}

function onSearchMapClick(e) {
  const { lat, lng } = e.latlng;
  if (mapClickMode === 'pickup') {
    setPickup(lat, lng, `${lat.toFixed(5)}, ${lng.toFixed(5)}`);
    mapClickMode = 'dropoff';
    updateMapHint('Haz clic en el mapa para colocar tu destino');
    document.getElementById('btn-pin-pickup').classList.remove('active');
    document.getElementById('btn-pin-dropoff').classList.add('active');
  } else if (mapClickMode === 'dropoff') {
    setDropoff(lat, lng, `${lat.toFixed(5)}, ${lng.toFixed(5)}`);
    mapClickMode = null;
    updateMapHint('');
    document.getElementById('btn-pin-dropoff').classList.remove('active');
    hideMapHint();
  } else {
    // Auto mode: first click = pickup, second = dropoff
    if (!pickupState) {
      setPickup(lat, lng, `${lat.toFixed(5)}, ${lng.toFixed(5)}`);
      updateMapHint('Ahora haz clic para colocar tu destino');
    } else if (!dropoffState) {
      setDropoff(lat, lng, `${lat.toFixed(5)}, ${lng.toFixed(5)}`);
      hideMapHint();
    }
  }
}

function updateMapHint(text) {
  const hint = document.getElementById('map-hint');
  hint.style.display = text ? 'flex' : 'none';
  hint.childNodes[1] ? (hint.lastChild.textContent = ' ' + text) : null;
}

function hideMapHint() {
  document.getElementById('map-hint').style.display = 'none';
}

function createCustomIcon(cls, label) {
  return L.divIcon({
    html: `<div class="custom-marker ${cls}">${label}</div>`,
    className: '',
    iconSize: [32, 32],
    iconAnchor: [16, 16]
  });
}

function setPickup(lat, lng, label) {
  pickupState = { lat, lng };
  document.getElementById('pickup-input').value = label;
  document.getElementById('pickup-coords-display').textContent = `${lat.toFixed(5)}, ${lng.toFixed(5)}`;
  if (pickupMarker) searchMap.removeLayer(pickupMarker);
  pickupMarker = L.marker([lat, lng], { icon: createCustomIcon('marker-pickup', 'A') }).addTo(searchMap);
  searchMap.panTo([lat, lng]);
}

function setDropoff(lat, lng, label) {
  dropoffState = { lat, lng };
  document.getElementById('dropoff-input').value = label;
  document.getElementById('dropoff-coords-display').textContent = `${lat.toFixed(5)}, ${lng.toFixed(5)}`;
  if (dropoffMarker) searchMap.removeLayer(dropoffMarker);
  dropoffMarker = L.marker([lat, lng], { icon: createCustomIcon('marker-dropoff', 'B') }).addTo(searchMap);
  if (pickupState) {
    const bounds = L.latLngBounds([[pickupState.lat, pickupState.lng], [lat, lng]]);
    searchMap.fitBounds(bounds, { padding: [40, 40] });
  }
}

function resetMap() {
  pickupState = null;
  dropoffState = null;
  if (pickupMarker) { searchMap.removeLayer(pickupMarker); pickupMarker = null; }
  if (dropoffMarker) { searchMap.removeLayer(dropoffMarker); dropoffMarker = null; }
  document.getElementById('pickup-input').value = '';
  document.getElementById('dropoff-input').value = '';
  document.getElementById('pickup-coords-display').textContent = '';
  document.getElementById('dropoff-coords-display').textContent = '';
  mapClickMode = null;
  updateMapHint('Haz clic en el mapa para colocar tu punto de recogida');
  document.getElementById('map-hint').style.display = 'flex';
  searchMap.setView([25.70, -100.32], 11);
}

// ---- PRESETS ----
function initPresets() {
  const grid = document.getElementById('presets-grid');
  PASAJEROS_TESTS.forEach((test, i) => {
    const card = document.createElement('div');
    card.className = 'preset-card';
    card.innerHTML = `
      <div class="preset-num">Caso ${i+1}</div>
      <div class="preset-name">${test.description}</div>
    `;
    card.addEventListener('click', () => loadPreset(i, card));
    grid.appendChild(card);
  });
}

function loadPreset(idx, cardEl) {
  // Deactivate others
  document.querySelectorAll('.preset-card').forEach(c => c.classList.remove('active'));
  cardEl.classList.add('active');

  const test = PASAJEROS_TESTS[idx];
  setPickup(parseFloat(test.pickup_lat), parseFloat(test.pickup_lng), test.pickup_address);
  setDropoff(parseFloat(test.dropoff_lat), parseFloat(test.dropoff_lng), test.dropoff_address);
}

// ---- RENDER RESULTS ----
let lastResults = [];

function renderResults(results, pickup, dropoff) {
  lastResults = results;
  const section = document.getElementById('results-section');
  section.classList.remove('hidden');
  document.getElementById('nav-results').style.display = 'block';

  const title = document.getElementById('results-title');
  const sub = document.getElementById('results-sub');
  title.textContent = results.length > 0 ? `${results.length} ruta${results.length > 1 ? 's' : ''} encontrada${results.length > 1 ? 's' : ''}` : 'Sin rutas compatibles';
  sub.textContent = results.length > 0
    ? `Mostrando las mejores coincidencias para tu trayecto · Algoritmo anti-backtracking activado`
    : 'No se encontraron conductores que vayan en tu dirección sin backtracking.';

  // Draw on results map
  drawResultsMap(results, pickup, dropoff);

  // Render sidebar
  renderSidebar(results);

  // Render full list
  renderFullList(results);

  setTimeout(() => {
    section.scrollIntoView({ behavior: 'smooth', block: 'start' });
    if (resultsMap) setTimeout(() => resultsMap.invalidateSize(), 200);
  }, 100);
}

function drawResultsMap(results, pickup, dropoff) {
  // Clear previous
  routePolylines.forEach(p => resultsMap.removeLayer(p));
  routePolylines = [];
  resultsMap.eachLayer(l => { if (l instanceof L.Marker) resultsMap.removeLayer(l); });

  if (results.length === 0) return;

  const bounds = L.latLngBounds();

  // Draw routes
  results.forEach((res, i) => {
    const color = ROUTE_COLORS[i] || '#CCCCCC';
    const weight = i === 0 ? 5 : i === 1 ? 4 : 3;
    const poly = L.polyline(res.waypoints, { color, weight, opacity: i === 0 ? 0.95 : 0.55 });
    poly.addTo(resultsMap);

    // Popup
    poly.bindPopup(`
      <div class="route-popup">
        <h4>#${i+1} ${res.conductor.driver_name}</h4>
        <p><span class="score-big">${(res.score * 100).toFixed(0)}%</span> compatibilidad</p>
        <p>🚗 ${res.conductor.vehicle_type} · ${res.conductor.seats_available} asientos</p>
        <p>⏰ ${res.conductor.departure_time} → ${res.conductor.arrival_time}</p>
        <p>📍 ${res.pickupDist}m al inicio · ${res.dropoffDist}m al destino</p>
        <p>✅ Cobertura: ${res.coverage_pct}%</p>
      </div>
    `);

    poly.on('mouseover', () => { poly.setStyle({ opacity: 1, weight: weight + 1 }); });
    poly.on('mouseout', () => { poly.setStyle({ opacity: i === 0 ? 0.95 : 0.55, weight }); });

    routePolylines.push(poly);
    res.waypoints.forEach(wp => bounds.extend(wp));
  });

  // Pickup / dropoff markers
  L.marker([pickup.lat, pickup.lng], { icon: createCustomIcon('marker-pickup', 'A'), zIndexOffset: 1000 })
    .bindPopup('<b>Punto de recogida</b>')
    .addTo(resultsMap);
  L.marker([dropoff.lat, dropoff.lng], { icon: createCustomIcon('marker-dropoff', 'B'), zIndexOffset: 1000 })
    .bindPopup('<b>Tu destino</b>')
    .addTo(resultsMap);

  bounds.extend([pickup.lat, pickup.lng]);
  bounds.extend([dropoff.lat, dropoff.lng]);

  resultsMap.fitBounds(bounds, { padding: [32, 32] });
}

function highlightRoute(idx) {
  routePolylines.forEach((p, i) => {
    const weight = i === 0 ? 5 : i === 1 ? 4 : 3;
    if (i === idx) {
      p.setStyle({ opacity: 1, weight: weight + 2, color: ROUTE_COLORS[i] });
      p.bringToFront();
    } else {
      p.setStyle({ opacity: 0.2, weight });
    }
  });
}

function resetRouteHighlight() {
  routePolylines.forEach((p, i) => {
    const weight = i === 0 ? 5 : i === 1 ? 4 : 3;
    p.setStyle({ opacity: i === 0 ? 0.95 : 0.55, weight, color: ROUTE_COLORS[i] });
  });
}

function renderSidebar(results) {
  const sidebar = document.getElementById('sidebar-routes');
  sidebar.innerHTML = '';
  if (results.length === 0) {
    sidebar.innerHTML = '<div style="padding:24px;text-align:center;color:#888;font-size:0.85rem;">Sin resultados para este trayecto</div>';
    return;
  }
  results.forEach((res, i) => {
    const c = res.conductor;
    const card = document.createElement('div');
    card.className = `sidebar-route-card${i === 0 ? ' active' : ''}`;
    card.innerHTML = `
      <div class="src-header">
        <div class="src-rank">
          <div class="rank-badge rank-${i+1}">${i+1}</div>
          <div class="driver-name-sm">${c.driver_name}</div>
        </div>
        <div class="score-pill ${res.score < 0.5 ? 'low' : ''}">${(res.score * 100).toFixed(0)}%</div>
      </div>
      <div class="src-details">
        <div class="src-detail">🚗 <strong>${c.vehicle_type}</strong></div>
        <div class="src-detail">⏰ <strong>${c.departure_time}</strong></div>
        <div class="src-detail">💺 <strong>${c.seats_available} asientos</strong></div>
        <div class="src-detail">📍 ${res.pickupDist}m / ${res.dropoffDist}m</div>
        <div class="src-detail">✅ ${res.coverage_pct}% cobertura</div>
      </div>
    `;
    card.addEventListener('mouseenter', () => {
      document.querySelectorAll('.sidebar-route-card').forEach(c => c.classList.remove('active'));
      card.classList.add('active');
      highlightRoute(i);
      if (routePolylines[i]) resultsMap.panTo(routePolylines[i].getBounds().getCenter());
    });
    card.addEventListener('mouseleave', () => { resetRouteHighlight(); });
    card.addEventListener('click', () => {
      document.getElementById('tab-list').click();
      const listCard = document.querySelectorAll('.route-card-full')[i];
      if (listCard) listCard.scrollIntoView({ behavior: 'smooth', block: 'center' });
    });
    sidebar.appendChild(card);
  });
}

function renderFullList(results) {
  const list = document.getElementById('routes-list');
  list.innerHTML = '';
  if (results.length === 0) {
    list.innerHTML = '<div style="text-align:center;padding:64px;color:#888;">No se encontraron rutas compatibles. Intenta ampliar la ventana horaria o ajusta tus puntos.</div>';
    return;
  }
  results.forEach((res, i) => {
    const c = res.conductor;
    const scoreVal = (res.score * 100).toFixed(0);
    const rankCls = ['r1','r2','r3','r4','r5'][i];
    const card = document.createElement('div');
    card.className = `route-card-full ${i === 0 ? 'rank-1' : ''}`;
    card.innerHTML = `
      <div class="rcf-header">
        <div class="rcf-rank-name">
          <div class="rcf-rank-badge ${rankCls}">${i+1}</div>
          <div class="rcf-driver-info">
            <h3>${c.driver_name}</h3>
            <p>ID Conductor: ${c.driver_id} · Ruta: ${c.route_id}</p>
          </div>
        </div>
        <div class="rcf-score-block">
          <div class="rcf-score-num">${scoreVal}%</div>
          <div class="rcf-score-label">Compatibilidad</div>
          <div class="rcf-score-bar"><div class="rcf-score-fill" style="width:${scoreVal}%"></div></div>
        </div>
      </div>

      <div class="rcf-grid">
        <div class="rcf-metric">
          <div class="rcf-metric-label">Proximidad</div>
          <div class="rcf-metric-val highlight">${(res.proxScore * 100).toFixed(0)}%</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Cobertura del viaje</div>
          <div class="rcf-metric-val highlight">${res.coverage_pct}%</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Horario</div>
          <div class="rcf-metric-val highlight">${(res.scheduleScore * 100).toFixed(0)}%</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Desvío estimado</div>
          <div class="rcf-metric-val ${res.detourMeters > 1500 ? '' : 'highlight'}">${res.detourMeters}m</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Distancia pickup</div>
          <div class="rcf-metric-val">${res.pickupDist}m</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Distancia dropoff</div>
          <div class="rcf-metric-val">${res.dropoffDist}m</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Segmento compartido</div>
          <div class="rcf-metric-val">${res.sharedKm} km</div>
        </div>
        <div class="rcf-metric">
          <div class="rcf-metric-label">Viaje pasajero</div>
          <div class="rcf-metric-val">${res.passengerKm} km</div>
        </div>
      </div>

      <div class="rcf-route-info">
        <div class="rcf-route-col">
          <label>Origen del conductor</label>
          <p>${c.origin_address}</p>
        </div>
        <div class="rcf-route-col">
          <label>Destino del conductor</label>
          <p>${c.destination_address}</p>
        </div>
        <div class="rcf-route-col">
          <label>Horario</label>
          <p>Salida: <strong>${c.departure_time}</strong> · Llegada: <strong>${c.arrival_time}</strong></p>
          <p>${c.distance_km} km · ${c.estimated_duration_min} min estimado</p>
        </div>
        <div class="rcf-route-col">
          <label>Vehículo y disponibilidad</label>
          <p>
            <span class="vehicle-badge">${getVehicleIcon(c.vehicle_type)} ${c.vehicle_type}</span>
            <span class="seats-badge">💺 ${c.seats_available} asientos disponibles</span>
          </p>
          <p style="margin-top:6px;font-size:0.78rem;color:#888;">Fecha: ${c.date}</p>
        </div>
      </div>
    `;
    list.appendChild(card);
  });
}

function getVehicleIcon(type) {
  const icons = { 'suv': '🚙', 'sedan': '🚗', 'hatchback': '🚘', 'pickup': '🛻' };
  return icons[type] || '🚗';
}

// ---- EVENT LISTENERS ----
function initEventListeners() {
  // Tab switching
  document.getElementById('tab-map').addEventListener('click', () => {
    document.getElementById('tab-map').classList.add('active');
    document.getElementById('tab-list').classList.remove('active');
    document.getElementById('map-view').classList.remove('hidden');
    document.getElementById('list-view').classList.add('hidden');
    setTimeout(() => resultsMap && resultsMap.invalidateSize(), 100);
  });
  document.getElementById('tab-list').addEventListener('click', () => {
    document.getElementById('tab-list').classList.add('active');
    document.getElementById('tab-map').classList.remove('active');
    document.getElementById('list-view').classList.remove('hidden');
    document.getElementById('map-view').classList.add('hidden');
  });

  // Pin buttons
  document.getElementById('btn-pin-pickup').addEventListener('click', () => {
    mapClickMode = 'pickup';
    document.getElementById('btn-pin-pickup').classList.add('active');
    document.getElementById('btn-pin-dropoff').classList.remove('active');
    document.getElementById('map-hint').style.display = 'flex';
    updateMapHint('Haz clic en el mapa para colocar tu punto de recogida');
  });
  document.getElementById('btn-pin-dropoff').addEventListener('click', () => {
    mapClickMode = 'dropoff';
    document.getElementById('btn-pin-dropoff').classList.add('active');
    document.getElementById('btn-pin-pickup').classList.remove('active');
    document.getElementById('map-hint').style.display = 'flex';
    updateMapHint('Haz clic en el mapa para colocar tu destino');
  });

  // Reset
  document.getElementById('map-reset-btn').addEventListener('click', resetMap);

  // Search button
  document.getElementById('btn-search').addEventListener('click', runSearch);
}

async function runSearch() {
  if (!pickupState || !dropoffState) {
    alert('Por favor selecciona un punto de recogida y un destino en el mapa o usa los casos de prueba.');
    return;
  }

  const overlay = document.getElementById('loading-overlay');
  overlay.classList.remove('hidden');

  // Small delay for UX
  await new Promise(r => setTimeout(r, 400));

  const desiredTime = document.getElementById('desired-time').value;
  const timeWindow = parseInt(document.getElementById('time-window').value);

  const results = findBestRoutes(pickupState, dropoffState, desiredTime, timeWindow);
  overlay.classList.add('hidden');
  renderResults(results, pickupState, dropoffState);
}

// ---- INIT ----
document.addEventListener('DOMContentLoaded', async () => {
  await loadData();
  initMaps();
  initEventListeners();

  // Show map hint on load
  document.getElementById('map-hint').style.display = 'flex';

  // Smooth reveal animations
  const observer = new IntersectionObserver((entries) => {
    entries.forEach(e => {
      if (e.isIntersecting) {
        e.target.style.opacity = '1';
        e.target.style.transform = 'translateY(0)';
      }
    });
  }, { threshold: 0.1 });

  document.querySelectorAll('.how-card, .search-card').forEach(el => {
    el.style.opacity = '0';
    el.style.transform = 'translateY(20px)';
    el.style.transition = 'opacity 0.5s ease, transform 0.5s ease';
    observer.observe(el);
  });
});
