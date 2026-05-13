# Sistema-de-ruta-optimizada

# RouteOPT — Optimizador de Rutas de Delivery

Aplicación web para calcular rutas óptimas de entrega en Medellín.  
Combina tres algoritmos clásicos de grafos para resolver el problema completo: orden de visita, camino más corto y rutas alternativas.

---

## Estructura del proyecto

```
delivery_optimizer/
├── app.py                  ← Backend Python (Flask + algoritmos)
├── requirements.txt        ← Dependencias
├── README.md               ← Este archivo
└── templates/
    └── index.html          ← Interfaz web (HTML + CSS + JS)
```

---

## Requisitos

- Python 3.8 o superior
- Conexión a internet (para cargar el mapa y consultar OSRM)

---

## Instalación y ejecución

```bash
# 1. Instalar dependencias (solo la primera vez)
pip install flask

# 2. Ejecutar el servidor
python app.py

# 3. Abrir en el navegador
http://localhost:5000
```

---

## Cómo usar la aplicación

1. Seleccionar un **punto de origen** en el panel izquierdo.
2. Agregar uno o más **puntos de entrega** con el botón `+`.
3. Hacer clic en **"Calcular rutas óptimas"**.
4. El sistema muestra el **orden óptimo de visita** (TSP) y las **3 mejores rutas**.
5. Al hacer clic en una tarjeta de ruta, el mapa resalta esa ruta sobre las calles reales.

> El orden en que se ingresan los destinos no importa — el algoritmo TSP los reordena automáticamente para minimizar el recorrido total.

---

## Algoritmos implementados

### 1. Dijkstra
Calcula el camino de menor costo entre dos nodos del grafo.  
Se ejecuta una vez por cada par de paradas para construir la matriz de costos que usa el TSP.

- **Estructura usada:** cola de prioridad (min-heap con `heapq`)
- **Complejidad:** O((V + E) log V)

### 2. Algoritmo de Yen (K caminos más cortos)
Dado un par origen-destino, genera las K rutas más cortas sin repetir la anterior.  
Se usa para producir las 3 variantes de ruta que el usuario puede comparar.

- **Estrategia:** bloquea aristas y nodos de caminos ya encontrados para forzar desvíos controlados
- **Complejidad:** O(K · V · (V + E) log V)

### 3. TSP — Problema del Viajero
Determina el orden óptimo de visita de todos los destinos antes de calcular la ruta.

| Cantidad de destinos | Algoritmo usado | Detalle |
|---|---|---|
| ≤ 8 | Fuerza bruta | Evalúa todas las permutaciones (máx. 8! = 40.320) |
| > 8 | Greedy (vecino más cercano) | Siempre elige el destino más cercano no visitado |

### Flujo completo de cálculo

```
Destinos ingresados
       ↓
  [TSP] Reordenar destinos para minimizar costo total
       ↓
  [Dijkstra] Calcular camino mínimo entre cada par de paradas
       ↓
  [Yen] Generar 2 variantes alternativas de la ruta óptima
       ↓
  [OSRM] Trazar cada ruta sobre calles reales de Medellín
       ↓
  Mostrar las 3 mejores rutas ordenadas por costo
```

---

## Estructuras de datos

| Estructura | Uso en el proyecto |
|---|---|
| **Grafo ponderado** | Representa el mapa de Medellín (clase `Grafo` con lista de adyacencia) |
| **Lista de adyacencia** | `dict[nodo] -> [(vecino, peso)]` — almacena conexiones entre nodos |
| **Cola de prioridad (min-heap)** | `heapq` en Dijkstra para procesar siempre el nodo de menor costo |
| **Conjunto (set)** | Nodos y aristas bloqueadas en el algoritmo de Yen |
| **Diccionario de matrices** | `dict[(u,v)] -> (costo, camino)` para la matriz de costos del TSP |

---

## Mapa de Medellín — Nodos del grafo

| ID | Lugar | Coordenadas |
|---|---|---|
| A | Parque de Bolívar | 6.2518, -75.5636 |
| B | El Poblado (Parque) | 6.2086, -75.5674 |
| C | Laureles (Estadio) | 6.2442, -75.5908 |
| D | Bello (Centro) | 6.3367, -75.5572 |
| E | Itagüí (Centro) | 6.1844, -75.5996 |
| F | Envigado (Parque) | 6.1751, -75.5908 |
| G | Sabaneta (Parque) | 6.1514, -75.6175 |
| H | La América | 6.2508, -75.6008 |
| I | Robledo | 6.2805, -75.5986 |
| J | Aranjuez | 6.2845, -75.5602 |
| K | Castilla | 6.3005, -75.5751 |
| L | Belén (Rosales) | 6.2264, -75.6109 |
| M | El Centro (Alpujarra) | 6.2416, -75.5728 |
| N | Guayabal | 6.2175, -75.5968 |
| O | Santa Fe | 6.2622, -75.5538 |

Los pesos de las aristas representan **tiempo estimado de viaje en minutos** entre nodos conectados.

---

## Tecnologías y recursos

### Backend
| Recurso | Tipo | Uso |
|---|---|---|
| Python 3.8+ | Lenguaje | Lógica de algoritmos |
| Flask | Librería externa | Servidor web y endpoints API REST |
| `heapq` | Librería estándar | Cola de prioridad para Dijkstra |
| `math` | Librería estándar | `math.inf` para distancias iniciales |
| `itertools.permutations` | Librería estándar | TSP por fuerza bruta |

### Frontend
| Recurso | Tipo | Uso |
|---|---|---|
| HTML / CSS / JavaScript | Nativo del navegador | Interfaz de usuario |
| Fetch API | Nativo del navegador | Llamadas al backend Flask y a OSRM |
| Leaflet.js 1.9.4 | Librería JS (CDN) | Mapa interactivo y dibujo de rutas |

### APIs y servicios externos
| Servicio | API key | Uso |
|---|---|---|
| OSRM (`router.project-osrm.org`) | No requerida | Traza rutas sobre calles reales (llamado desde el navegador) |
| CartoDB Positron | No requerida | Tiles del mapa blanco |
| OpenStreetMap | No requerida | Fuente de datos geográficos base |
| Google Fonts | No requerida | Tipografías Syne y Space Mono |

---

## Endpoints de la API

| Método | Ruta | Descripción |
|---|---|---|
| `GET` | `/` | Sirve la interfaz web |
| `GET` | `/api/nodos` | Retorna todos los nodos del grafo con coordenadas |
| `GET` | `/api/aristas` | Retorna todas las aristas con sus pesos |
| `POST` | `/api/calcular` | Recibe origen y destinos, retorna rutas optimizadas |

### Ejemplo de request a `/api/calcular`

```json
{
  "origen": "A",
  "destinos": ["D", "I", "K"]
}
```

### Ejemplo de response

```json
{
  "orden_optimo": ["A", "D", "K", "I"],
  "rutas": [
    {
      "costo": 38,
      "nodos": [
        { "id": "A", "nombre": "Parque de Bolívar", "lat": 6.2518, "lon": -75.5636 },
        { "id": "J", "nombre": "Aranjuez", "lat": 6.2845, "lon": -75.5602 },
        "..."
      ]
    }
  ]
}
```

---

## Notas de arquitectura

**¿Por qué OSRM se llama desde el navegador y no desde Python?**  
El servidor Flask corre en un entorno local sin acceso irrestricto a internet externo. El navegador del usuario sí puede consultar la API pública de OSRM directamente. Por eso la arquitectura separa las responsabilidades: Python resuelve los algoritmos de grafos, y el navegador le pide a OSRM la geometría real de cada ruta para dibujarla sobre las calles.

**Fallback automático:**  
Si OSRM no responde, la aplicación dibuja las rutas como líneas rectas entre los nodos del grafo e indica esto en la tarjeta de cada ruta.
