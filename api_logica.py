from flask import Flask, request, jsonify
from flask_cors import CORS
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import seaborn as sns
import io
import base64
import heapq
from collections import deque

servidor = Flask(__name__)
CORS(servidor)


grafo_redirecciones = {
    "Enlace_Original": ["Servidor_Proxy", "Redireccion_Oculta"],
    "Servidor_Proxy": ["Enlace_Original", "Servidor_Malicioso"], 
    "Redireccion_Oculta": ["Anuncio_Falso", "Servidor_Malicioso"],
    "Anuncio_Falso": ["Redireccion_Oculta"], 
    "Servidor_Malicioso": []
}

def buscar_trazabilidad_dfs(actual, objetivo, limite, prof=0, camino=None, visitados=None, rutas=None, orden=None):
    if camino is None: camino = []
    if visitados is None: visitados = set()
    if rutas is None: rutas = []
    if orden is None: orden = []

    orden.append(actual)
    visitados_actual = visitados.copy()
    visitados_actual.add(actual)
    camino_actual = camino + [actual]

    if prof > limite: return rutas, orden
    if actual == objetivo:
        rutas.append(camino_actual)
        return rutas, orden

    for vecino in grafo_redirecciones.get(actual, []):
        if vecino not in visitados_actual:
            buscar_trazabilidad_dfs(vecino, objetivo, limite, prof + 1, camino_actual, visitados_actual, rutas, orden)
    return rutas, orden


# 2. GRAFO DE COSTOS Y HEURÍSTICA 
grafo_costos = {
    'Inicio_Analisis (A)': {'Verificar_Remitente (B)': 2, 'Analizar_Enlace (C)': 5},
    'Verificar_Remitente (B)': {'Checar_Firma_Digital (D)': 4, 'Analizar_Texto (E)': 1},
    'Analizar_Enlace (C)': {'Buscar_Malware (F)': 2, 'Consultar_Lista_Negra (G)': 8},
    'Checar_Firma_Digital (D)': {'Evaluar_Certificado (H)': 3},
    'Analizar_Texto (E)': {'Procesamiento_Lenguaje (I)': 2},
    'Buscar_Malware (F)': {'Dictamen_Final (J)': 3},
    'Consultar_Lista_Negra (G)': {},
    'Evaluar_Certificado (H)': {},
    'Procesamiento_Lenguaje (I)': {},
    'Dictamen_Final (J)': {}
}

heuristica_safeguard = {
    'Inicio_Analisis (A)': 7, 'Verificar_Remitente (B)': 6, 'Analizar_Enlace (C)': 4,
    'Checar_Firma_Digital (D)': 7, 'Analizar_Texto (E)': 5, 'Buscar_Malware (F)': 3,
    'Consultar_Lista_Negra (G)': 6, 'Evaluar_Certificado (H)': 8,
    'Procesamiento_Lenguaje (I)': 1, 'Dictamen_Final (J)': 0
}


# 3. IMPLEMENTACIÓN DE LOS 5 ALGORITMOS 
def reconstruir_camino(padres, inicio, objetivo):
    if objetivo not in padres and objetivo != inicio: return []
    camino = [objetivo]
    actual = objetivo
    while actual != inicio:
        actual = padres.get(actual)
        if actual is None: return []
        camino.append(actual)
    camino.reverse()
    return camino

def calcular_costo_real(grafo, camino):
    if not camino: return 0
    return sum(grafo[camino[i]].get(camino[i+1], 0) for i in range(len(camino)-1))

# 3.1 BFS
def busqueda_bfs(grafo, inicio, objetivo):
    frontera = deque([inicio])
    descubiertos = {inicio}
    padres = {inicio: None}
    while frontera:
        actual = frontera.popleft()
        if actual == objetivo: break
        for vecino in grafo.get(actual, {}):
            if vecino not in descubiertos:
                descubiertos.add(vecino)
                padres[vecino] = actual
                frontera.append(vecino)
    camino = reconstruir_camino(padres, inicio, objetivo)
    return camino, calcular_costo_real(grafo, camino)

# 3.2 DFS Clásico
def busqueda_dfs(grafo, inicio, objetivo):
    pila = [inicio]
    descubiertos = {inicio}
    padres = {inicio: None}
    while pila:
        actual = pila.pop()
        if actual == objetivo: break
        for vecino in reversed(list(grafo.get(actual, {}).keys())):
            if vecino not in descubiertos:
                descubiertos.add(vecino)
                padres[vecino] = actual
                pila.append(vecino)
    camino = reconstruir_camino(padres, inicio, objetivo)
    return camino, calcular_costo_real(grafo, camino)

# 3.3 UCS
def busqueda_ucs(grafo, inicio, objetivo):
    frontera = [(0, inicio)]
    mejor_costo = {inicio: 0}
    padres = {inicio: None}
    cerrados = set()
    while frontera:
        costo_actual, actual = heapq.heappop(frontera)
        if actual in cerrados: continue
        cerrados.add(actual)
        if actual == objetivo: break
        for vecino, peso in grafo.get(actual, {}).items():
            nuevo_costo = costo_actual + peso
            if nuevo_costo < mejor_costo.get(vecino, float('inf')):
                mejor_costo[vecino] = nuevo_costo
                padres[vecino] = actual
                heapq.heappush(frontera, (nuevo_costo, vecino))
    camino = reconstruir_camino(padres, inicio, objetivo)
    return camino, mejor_costo.get(objetivo, 0) if camino else 0

# 3.4 Greedy
def busqueda_greedy(grafo, inicio, objetivo, heuristica):
    h = heuristica if objetivo == 'Dictamen_Final (J)' else {n: 0 for n in grafo}
    frontera = [(h.get(inicio, 0), inicio)]
    descubiertos = {inicio}
    padres = {inicio: None}
    while frontera:
        _, actual = heapq.heappop(frontera)
        if actual == objetivo: break
        for vecino in grafo.get(actual, {}):
            if vecino not in descubiertos:
                descubiertos.add(vecino)
                padres[vecino] = actual
                heapq.heappush(frontera, (h.get(vecino, 0), vecino))
    camino = reconstruir_camino(padres, inicio, objetivo)
    return camino, calcular_costo_real(grafo, camino)

# 3.5 A*
def busqueda_astar(grafo, inicio, objetivo, heuristica):
    h_dict = heuristica if objetivo == 'Dictamen_Final (J)' else {n: 0 for n in grafo}
    cola = [(h_dict.get(inicio, 0), inicio, [inicio], 0)]
    visitados = set()
    nodos_explorados = [] 

    while cola:
        fn, nodo_actual, camino, gn = heapq.heappop(cola)
        if nodo_actual in visitados: continue
        visitados.add(nodo_actual)
        nodos_explorados.append({
            "nodo": nodo_actual, "gn": gn, "hn": h_dict.get(nodo_actual, 0), "fn": fn
        })
        if nodo_actual == objetivo:
            return camino, gn, nodos_explorados

        for vecino, costo_paso in grafo.get(nodo_actual, {}).items():
            if vecino not in visitados:
                nuevo_gn = gn + costo_paso
                hn = h_dict.get(vecino, 0)
                nuevo_fn = nuevo_gn + hn
                heapq.heappush(cola, (nuevo_fn, vecino, camino + [vecino], nuevo_gn))

    return [], 0, nodos_explorados


def generar_grafica_matplotlib():
    plt.figure(figsize=(9, 4))
    sns.set_theme(style="whitegrid")
    meses = ["Jul", "Ago", "Sep", "Oct", "Nov", "Dic"]
    valores = [120, 150, 180, 320, 410, 480]
    plt.plot(meses, valores, color='#dc3545', marker='o', linewidth=3, markersize=8)
    plt.fill_between(meses, valores, color='#dc3545', alpha=0.1)
    plt.title('Tendencia de Amenazas', fontsize=14, fontweight='bold', pad=15)
    plt.ylabel('Cantidad de Reportes')
    
    buf = io.BytesIO()
    plt.savefig(buf, format='png', bbox_inches='tight', dpi=120)
    buf.seek(0)
    plt.close()
    return base64.b64encode(buf.read()).decode('utf-8')


@servidor.route('/analizar_avanzado', methods=['POST'])
def evaluar_seguridad_completa():
    datos = request.json or {}
    
    # NUEVA LÓGICA: Si viene la bandera "modo_laboratorio", se ejecuta solo lo del final
    if datos.get('modo_laboratorio', False):
        nodo_inicio = datos.get('inicio', 'A')
        nodo_objetivo = datos.get('objetivo', 'J')
        algoritmo_seleccionado = datos.get('algoritmo', 'A*')

        nombres_completos = {
            'A': 'Inicio_Analisis (A)', 'B': 'Verificar_Remitente (B)', 'C': 'Analizar_Enlace (C)',
            'D': 'Checar_Firma_Digital (D)', 'E': 'Analizar_Texto (E)', 'F': 'Buscar_Malware (F)',
            'G': 'Consultar_Lista_Negra (G)', 'H': 'Evaluar_Certificado (H)', 'I': 'Procesamiento_Lenguaje (I)',
            'J': 'Dictamen_Final (J)'
        }
        
        inicio_full = nombres_completos.get(nodo_inicio, 'Inicio_Analisis (A)')
        objetivo_full = nombres_completos.get(nodo_objetivo, 'Dictamen_Final (J)')

        ruta_bfs, costo_bfs = busqueda_bfs(grafo_costos, inicio_full, objetivo_full)
        ruta_dfs, costo_dfs = busqueda_dfs(grafo_costos, inicio_full, objetivo_full)
        ruta_ucs, costo_ucs = busqueda_ucs(grafo_costos, inicio_full, objetivo_full)
        ruta_grd, costo_grd = busqueda_greedy(grafo_costos, inicio_full, objetivo_full, heuristica_safeguard)
        ruta_ast, costo_ast, _ = busqueda_astar(grafo_costos, inicio_full, objetivo_full, heuristica_safeguard)

        comparativa = [
            {"algoritmo": "BFS (Anchura)", "ruta": ruta_bfs, "costo": costo_bfs},
            {"algoritmo": "DFS (Profundidad)", "ruta": ruta_dfs, "costo": costo_dfs},
            {"algoritmo": "UCS (Costo Uniforme)", "ruta": ruta_ucs, "costo": costo_ucs},
            {"algoritmo": "Greedy (Voraz)", "ruta": ruta_grd, "costo": costo_grd},
            {"algoritmo": "A* (Heurística)", "ruta": ruta_ast, "costo": costo_ast},
        ]

        ruta_animacion = []
        if algoritmo_seleccionado == 'BFS': ruta_animacion = ruta_bfs
        elif algoritmo_seleccionado == 'DFS': ruta_animacion = ruta_dfs
        elif algoritmo_seleccionado == 'UCS': ruta_animacion = ruta_ucs
        elif algoritmo_seleccionado == 'Greedy': ruta_animacion = ruta_grd
        elif algoritmo_seleccionado == 'A*': ruta_animacion = ruta_ast

        return jsonify({
            "comparativa_algoritmos": comparativa,
            "ruta_animacion": ruta_animacion
        })

    # LÓGICA ORIGINAL: Análisis de Ciberseguridad
    p = datos.get('tiene_enlace', False)
    q = datos.get('remitente_desconocido', False)
    r = datos.get('es_urgente', False)
    d = datos.get('es_contenido_sensible', False)
    limite_profundidad = int(datos.get('limite_profundidad', 3))

    resultado_phishing = p and (q or r)
    resultado_bloqueo = resultado_phishing or d
    resultado_seguro = not resultado_bloqueo

    rutas_dfs, orden_dfs = ([], [])
    if p:
        rutas_dfs, orden_dfs = buscar_trazabilidad_dfs("Enlace_Original", "Servidor_Malicioso", limite=limite_profundidad)

    nodo_meta = 'Procesamiento_Lenguaje (I)' if resultado_seguro else 'Dictamen_Final (J)'
    nodo_inicio = 'Inicio_Analisis (A)'

    ruta_bfs, costo_bfs = busqueda_bfs(grafo_costos, nodo_inicio, nodo_meta)
    ruta_dfs, costo_dfs = busqueda_dfs(grafo_costos, nodo_inicio, nodo_meta)
    ruta_ucs, costo_ucs = busqueda_ucs(grafo_costos, nodo_inicio, nodo_meta)
    ruta_grd, costo_grd = busqueda_greedy(grafo_costos, nodo_inicio, nodo_meta, heuristica_safeguard)
    ruta_ast, costo_ast, nodos_exp = busqueda_astar(grafo_costos, nodo_inicio, nodo_meta, heuristica_safeguard)

    comparativa = [
        {"algoritmo": "BFS (Anchura)", "ruta": ruta_bfs, "costo": costo_bfs},
        {"algoritmo": "DFS (Profundidad)", "ruta": ruta_dfs, "costo": costo_dfs},
        {"algoritmo": "UCS (Costo Uniforme)", "ruta": ruta_ucs, "costo": costo_ucs},
        {"algoritmo": "Greedy (Voraz)", "ruta": ruta_grd, "costo": costo_grd},
        {"algoritmo": "A* (Heurística)", "ruta": ruta_ast, "costo": costo_ast},
    ]

    grafica_python = generar_grafica_matplotlib()
    datos_grafica_web = {
        "etiquetas": ["Phishing", "Malware", "Contenido Sensible", "Spam"],
        "valores": [420, 315, 150, 580]
    }

    return jsonify({
        "es_phishing": resultado_phishing,
        "esta_bloqueado": resultado_bloqueo,
        "es_seguro": resultado_seguro,
        "dfs_orden_exploracion": orden_dfs,
        "dfs_rutas_encontradas": rutas_dfs,
        "astar_ruta_optima": ruta_ast,
        "astar_costo_total": costo_ast,
        "astar_nodos_explorados": nodos_exp,
        "comparativa_algoritmos": comparativa, 
        "grafica_python_base64": grafica_python,
        "datos_grafica_web": datos_grafica_web
    })

if __name__ == '__main__':
    servidor.run(debug=True, host='0.0.0.0', port=5000)