from flask import Flask, render_template, request, jsonify
import heapq
import json
import math

app = Flask(__name__)

# ─────────────────────────────────────────────
#  ESTRUCTURAS DE DATOS
# ─────────────────────────────────────────────

class Grafo:
    """Grafo ponderado con lista de adyacencia."""
    def __init__(self):
        self.nodos = {}          # id -> {nombre, lat, lon}
        self.adyacencia = {}     # id -> [(vecino, peso)]

    def agregar_nodo(self, nid, nombre, lat, lon):
        self.nodos[nid] = {"nombre": nombre, "lat": lat, "lon": lon}
        self.adyacencia.setdefault(nid, [])

    def agregar_arista(self, u, v, peso):
        self.adyacencia[u].append((v, peso))
        self.adyacencia[v].append((u, peso))   # bidireccional

    def vecinos(self, nid):
        return self.adyacencia.get(nid, [])


# ─────────────────────────────────────────────
#  ALGORITMO DE DIJKSTRA
# ─────────────────────────────────────────────

def dijkstra(grafo, origen):
    """
    Retorna (distancias, predecesores) desde `origen` a todos los nodos.
    Usa una cola de prioridad (min-heap).
    """
    dist = {nid: math.inf for nid in grafo.nodos}
    prev = {nid: None for nid in grafo.nodos}
    dist[origen] = 0

    heap = [(0, origen)]   # (costo acumulado, nodo)

    while heap:
        costo, u = heapq.heappop(heap)

        if costo > dist[u]:        # entrada obsoleta
            continue

        for v, peso in grafo.vecinos(u):
            nuevo_costo = dist[u] + peso
            if nuevo_costo < dist[v]:
                dist[v] = nuevo_costo
                prev[v] = u
                heapq.heappush(heap, (nuevo_costo, v))

    return dist, prev


def reconstruir_camino(prev, origen, destino):
    """Reconstruye el camino desde origen hasta destino usando predecesores."""
    camino = []
    actual = destino
    while actual is not None:
        camino.append(actual)
        actual = prev[actual]
    camino.reverse()
    if camino and camino[0] == origen:
        return camino
    return []


# ─────────────────────────────────────────────
#  ALGORITMO DE YEN (K caminos más cortos)
# ─────────────────────────────────────────────

def dijkstra_con_restricciones(grafo, origen, destino, nodos_bloqueados, aristas_bloqueadas):
    """
    Dijkstra que ignora nodos y aristas bloqueadas.
    Retorna (costo, camino) o (inf, []) si no hay camino.
    """
    if origen in nodos_bloqueados or destino in nodos_bloqueados:
        return math.inf, []

    dist = {nid: math.inf for nid in grafo.nodos}
    prev = {nid: None for nid in grafo.nodos}
    dist[origen] = 0
    heap = [(0, origen)]

    while heap:
        costo, u = heapq.heappop(heap)
        if costo > dist[u]:
            continue
        for v, peso in grafo.vecinos(u):
            if v in nodos_bloqueados:
                continue
            if (u, v) in aristas_bloqueadas or (v, u) in aristas_bloqueadas:
                continue
            nuevo = dist[u] + peso
            if nuevo < dist[v]:
                dist[v] = nuevo
                prev[v] = u
                heapq.heappush(heap, (nuevo, v))

    if math.isinf(dist[destino]):
        return math.inf, []

    return dist[destino], reconstruir_camino(prev, origen, destino)


def yen_k_caminos(grafo, origen, destino, k=3):
    """
    Algoritmo de Yen: retorna los k caminos más cortos entre origen y destino.
    Cada resultado es un dict {costo, camino}.
    """
    # Obtener el camino más corto inicial
    dist, prev = dijkstra(grafo, origen)
    if math.isinf(dist[destino]):
        return []

    camino_inicial = reconstruir_camino(prev, origen, destino)
    if not camino_inicial:
        return []

    A = [{"costo": dist[destino], "camino": camino_inicial}]  # caminos confirmados
    B = []   # candidatos (heap)

    for _ in range(k - 1):
        ultimo = A[-1]["camino"]

        for i in range(len(ultimo) - 1):
            nodo_spur = ultimo[i]
            camino_raiz = ultimo[:i + 1]
            costo_raiz = sum(
                _peso_arista(grafo, camino_raiz[j], camino_raiz[j+1])
                for j in range(len(camino_raiz) - 1)
            )

            aristas_bloqueadas = set()
            nodos_bloqueados = set()

            # Bloquear aristas de caminos previos que comparten la raíz
            for camino_prev in A:
                p = camino_prev["camino"]
                if len(p) > i and p[:i+1] == camino_raiz:
                    u, v = p[i], p[i+1]
                    aristas_bloqueadas.add((u, v))

            # Bloquear nodos de la raíz (excepto el spur)
            for nodo in camino_raiz[:-1]:
                nodos_bloqueados.add(nodo)

            costo_spur, camino_spur = dijkstra_con_restricciones(
                grafo, nodo_spur, destino, nodos_bloqueados, aristas_bloqueadas
            )

            if camino_spur:
                camino_total = camino_raiz[:-1] + camino_spur
                costo_total = costo_raiz + costo_spur

                entrada = {"costo": round(costo_total, 2), "camino": camino_total}
                # Evitar duplicados
                # En B los elementos son tuplas (costo, id, entrada), por eso usamos c[2]
                if not any(c[2]["camino"] == camino_total for c in B) and \
                   not any(c["camino"] == camino_total for c in A):
                    heapq.heappush(B, (costo_total, id(entrada), entrada))

        if not B:
            break

        _, _, mejor = heapq.heappop(B)
        A.append(mejor)

    return A


def _peso_arista(grafo, u, v):
    for vecino, peso in grafo.vecinos(u):
        if vecino == v:
            return peso
    return math.inf


# ─────────────────────────────────────────────
#  MAPA DE LA CIUDAD (grafo de ejemplo)
# ─────────────────────────────────────────────

def construir_ciudad():
    g = Grafo()

    # Ubicaciones reales de Medellín (lat, lon)
    nodos = [
        ("A", "Parque de Bolívar",          6.2518, -75.5636),
        ("B", "El Poblado (Parque)",        6.2086, -75.5674),
        ("C", "Laureles (Estadio)",         6.2442, -75.5908),
        ("D", "Bello (Centro)",             6.3367, -75.5572),
        ("E", "Itagüí (Centro)",            6.1844, -75.5996),
        ("F", "Envigado (Parque)",          6.1751, -75.5908),
        ("G", "Sabaneta (Parque)",          6.1514, -75.6175),
        ("H", "La América",                 6.2508, -75.6008),
        ("I", "Robledo",                    6.2805, -75.5986),
        ("J", "Aranjuez",                   6.2845, -75.5602),
        ("K", "Castilla",                   6.3005, -75.5751),
        ("L", "Belén (Rosales)",            6.2264, -75.6109),
        ("M", "El Centro (Alpujarra)",      6.2416, -75.5728),
        ("N", "Guayabal",                   6.2175, -75.5968),
        ("O", "Santa Fe",                   6.2622, -75.5538),
    ]

    for nid, nombre, lat, lon in nodos:
        g.agregar_nodo(nid, nombre, lat, lon)

    # Pesos en minutos (tiempo estimado de viaje por calles reales)
    aristas = [
        ("A","M",4),  ("A","O",6),  ("A","J",8),
        ("M","O",5),  ("M","C",12), ("M","H",10),
        ("O","J",7),  ("O","D",15),
        ("J","D",12), ("J","K",10),
        ("D","K",8),  ("D","I",14),
        ("K","I",10), ("K","C",18),
        ("I","C",12), ("I","H",8),
        ("C","H",7),  ("C","L",10),
        ("H","L",8),  ("H","N",9),
        ("L","N",6),  ("L","E",10), ("L","G",18),
        ("N","E",8),  ("N","B",10),
        ("E","F",6),  ("E","B",8),
        ("F","G",10), ("F","B",5),
        ("B","G",12),
    ]

    for u, v, p in aristas:
        g.agregar_arista(u, v, p)

    return g


CIUDAD = construir_ciudad()


# ─────────────────────────────────────────────
#  RUTAS FLASK
# ─────────────────────────────────────────────

@app.route("/")
def index():
    return render_template("index.html")


@app.route("/api/nodos")
def get_nodos():
    return jsonify(CIUDAD.nodos)


@app.route("/api/aristas")
def get_aristas():
    aristas = []
    vistas = set()
    for u, vecinos in CIUDAD.adyacencia.items():
        for v, peso in vecinos:
            clave = tuple(sorted([u, v]))
            if clave not in vistas:
                vistas.add(clave)
                aristas.append({"u": u, "v": v, "peso": peso})
    return jsonify(aristas)


# ─────────────────────────────────────────────
#  TSP — orden óptimo de visita (fuerza bruta
#  para n ≤ 8, greedy para más)
# ─────────────────────────────────────────────

def construir_matriz_costos(origen, destinos):
    """
    Calcula el costo mínimo (Dijkstra) entre todos los pares relevantes.
    Retorna dict (u,v) -> (costo, camino).
    """
    paradas = [origen] + destinos
    matriz  = {}
    for u in paradas:
        dist, prev = dijkstra(CIUDAD, u)
        for v in paradas:
            if u != v:
                camino = reconstruir_camino(prev, u, v)
                matriz[(u, v)] = (dist[v], camino)
    return matriz


def tsp_fuerza_bruta(origen, destinos, matriz):
    """
    Prueba todas las permutaciones de destinos y devuelve el orden
    con menor costo total. Viable hasta ~8 destinos (8! = 40320).
    """
    from itertools import permutations
    mejor_costo  = math.inf
    mejor_orden  = None

    for perm in permutations(destinos):
        paradas = [origen] + list(perm)
        costo   = sum(matriz[(paradas[i], paradas[i+1])][0]
                      for i in range(len(paradas)-1))
        if costo < mejor_costo:
            mejor_costo = costo
            mejor_orden = list(perm)

    return mejor_orden, mejor_costo


def tsp_greedy(origen, destinos, matriz):
    """
    Heurística del vecino más cercano para n > 8 destinos.
    """
    no_visitados = list(destinos)
    orden        = []
    actual       = origen

    while no_visitados:
        siguiente = min(no_visitados, key=lambda v: matriz[(actual, v)][0])
        orden.append(siguiente)
        no_visitados.remove(siguiente)
        actual = siguiente

    costo = sum(matriz[([origen]+orden)[i], ([origen]+orden)[i+1]][0]
                for i in range(len(orden)))
    return orden, costo


def ensamblar_camino(origen, orden, matriz):
    """
    Une los tramos Dijkstra para construir el camino completo
    en el orden TSP dado, sin repetir nodos de entrega ya visitados.
    """
    paradas      = [origen] + orden
    camino_total = [paradas[0]]
    costo_total  = 0

    for i in range(len(paradas) - 1):
        _, tramo = matriz[(paradas[i], paradas[i+1])]
        costo_total += matriz[(paradas[i], paradas[i+1])][0]
        camino_total += tramo[1:]   # evita duplicar el nodo de unión

    return {"costo": round(costo_total, 2), "camino": camino_total}


@app.route("/api/calcular", methods=["POST"])
def calcular():
    data     = request.get_json()
    origen   = data.get("origen")
    destinos = data.get("destinos", [])

    if not origen or not destinos:
        return jsonify({"error": "Se requiere origen y al menos un destino"}), 400
    if origen not in CIUDAD.nodos:
        return jsonify({"error": f"Nodo origen '{origen}' no existe"}), 400
    for d in destinos:
        if d not in CIUDAD.nodos:
            return jsonify({"error": f"Nodo destino '{d}' no existe"}), 400

    # ── Caso 1 destino: Yen directo ──
    if len(destinos) == 1:
        rutas = yen_k_caminos(CIUDAD, origen, destinos[0], k=3)
        if not rutas:
            return jsonify({"error": "No se encontró ruta entre los nodos"}), 404
        resultado = _serializar(rutas)
        return jsonify({"rutas": resultado, "orden_optimo": [origen] + destinos})

    # ── Múltiples destinos: TSP primero ──
    matriz = construir_matriz_costos(origen, destinos)

    # Verificar conectividad
    for (u, v), (costo, _) in matriz.items():
        if math.isinf(costo):
            return jsonify({"error": f"No hay camino entre {u} y {v}"}), 404

    # Elegir algoritmo según cantidad de destinos
    if len(destinos) <= 8:
        orden_optimo, _ = tsp_fuerza_bruta(origen, destinos, matriz)
    else:
        orden_optimo, _ = tsp_greedy(origen, destinos, matriz)

    # Ruta principal con el orden TSP óptimo
    ruta_base = ensamblar_camino(origen, orden_optimo, matriz)

    # Generar 2 variantes adicionales usando Yen en el primer tramo
    # manteniendo el orden TSP en el resto
    alternativas = [ruta_base]
    yen_primer   = yen_k_caminos(CIUDAD, origen, orden_optimo[0], k=4)

    for alt_tramo in yen_primer[1:]:
        if len(alternativas) >= 3:
            break
        # Reemplazar el primer tramo con la alternativa de Yen
        camino_alt = list(alt_tramo["camino"])
        costo_alt  = alt_tramo["costo"]

        # Encadenar el resto de paradas en orden TSP
        for i in range(len(orden_optimo) - 1):
            c, tramo = matriz[(orden_optimo[i], orden_optimo[i+1])]
            costo_alt  += c
            camino_alt += tramo[1:]

        entrada = {"costo": round(costo_alt, 2), "camino": camino_alt}
        if entrada["camino"] != ruta_base["camino"]:
            alternativas.append(entrada)

    alternativas = sorted(alternativas, key=lambda x: x["costo"])[:3]

    return jsonify({
        "rutas":        _serializar(alternativas),
        "orden_optimo": [origen] + orden_optimo,
    })


def _serializar(rutas):
    resultado = []
    for r in rutas:
        nodos_ruta = [
            {"id": nid, "nombre": CIUDAD.nodos[nid]["nombre"],
             "lat": CIUDAD.nodos[nid]["lat"], "lon": CIUDAD.nodos[nid]["lon"]}
            for nid in r["camino"]
        ]
        resultado.append({"costo": r["costo"], "nodos": nodos_ruta})
    return resultado


if __name__ == "__main__":
    app.run(debug=True, port=5000)
