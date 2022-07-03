from math import cos, e, gamma
import numpy as np
import random
from SyncRNG import SyncRNG
from numpy.core.arrayprint import printoptions
from numpy.core.fromnumeric import _nonzero_dispatcher, alltrue
from numpy.lib.twodim_base import triu_indices_from
from numpy.testing._private.nosetester import NoseTester
import seaborn as sb
import matplotlib.pyplot as plt
from seaborn.miscplot import dogplot
from seaborn.utils import desaturate, locator_to_legend_entries, move_legend
import sys
import copy
from queue import PriorityQueue
import time

"Lab 4.1. Búsqueda de las rutas más cortas"
"Lab 4.2. Busquedas dirigidas en el laberinto"


class Nodo:
    """
    Clase Nodo: Clase empleada para identificar cada nodo perteneciente al grafo.
    """
    def __init__(self, i):
        """
        Constructor:
            > id: identificar de cada nodo. Es de tipo int y es inicializado con el valor del parametro "i"
            > x: posicion que referida a la fila que ocupa cada nodo en la matriz de nodos
            > y: posicion que referida a la columna que ocupa cada nodo en la matriz de nodos
            > vecinos: lista que utilizo para almacenar los distintos vecinos que tiene un nodo en concreto junto con el peso que los relaciona
            > remove: atributo que utilizo para indicar si el nodo ha sido o no borrado del grafo durante el algoritmo de Dijkstra
            > distancia_tentativa: valor en el que almaceno la distancia tentativa de un nodo para el algoritmo de Dijsktra
        """
        self.id = i
        self.x = 0
        self.y = 0
        self.vecinos = []
        self.remove = False
        self.distancia_tentativa = sys.maxsize

    def agregaVecinoYPeso(self, lista_peso):
        """
        Funcion agregaVecinoYPeso: funcion mediante la cual agregamos un nuevo nodo a la lista de vecinos del nodo correspondiente
        · Parametros
            > self
            > lista_peso: lista a incluir en la lista de vecinos. Esta lista contiene tanto el nodo vecino como el peso del eje que los relaciona
        """
        if lista_peso[0] not in self.vecinos:
            self.vecinos.append(lista_peso)


class Grafo: 
    """
    Clase Grafo: clase empleada para representar el grafo
    """
    def __init__(self):
        """
        Constructor:
            > nodos: diccionario empleado para almacenar el conjunto de nodos que componen el grafo
        """
        self.nodos = {}

    def agregaNodo(self, n):
        """
        Procede a añadir en el diccionario de nodos un nuevo nodo que no se encuentre previamente guardado.
        · Parametros:
            > self
            > n: Nodo que se desea añadir al grafo
        """
        if n not in self.nodos:
            self.nodos[n] = Nodo(n) #Almacena objeto de tipo Nodo con su id
    
    def agregaEjes(self, n1, n2, peso):
        """
        Funcion agregaEjes: Funcion que crea los ejes entre los distintos nodos del grafo. Al tratarse de un grafo no direccionado, los ejes se crearan en un sentido
        y en el otro.
        Para llevar a cabo dicha tarea, lo que hago es llamar a la funcion "agregaVecinoYPeso" de la clase Nodo y le paso como argumento el nodo y el peso con el que se quiere crear el eje.
        · Parametros:
            > self
            > n1: Nodo recibido al que se le agregara como vecino el otro nodo enviado
            > n2: Nodo recibido al que se le agregara como vecino el otro nodo enviado
            > peso: peso que forma la conexion entre ambos nodos
        """
        #Grafo no direccionado
        if n1 not in self.nodos:
            self.agregaNodo(n1)

        if n2 not in self.nodos:
            self.agregaNodo(n2)

        #Creo 2 listas, en las que guardo el nodo vecino y el peso de ese eje
        lista_peso1 = [n2, peso]
        lista_peso2 = [n1, peso]
        self.nodos[n1].agregaVecinoYPeso(lista_peso1)
        self.nodos[n2].agregaVecinoYPeso(lista_peso2)



"""***************************************************************************************************************************************************

                                                                     DIJKSTRA CLASICO                                                                         

"***************************************************************************************************************************************************"""

def dist_min(g):
    """
    Funcion mediante la cual obtengo la distancia tentativa minima del grafo entre los nodos del grafo que no hayan sido borrados durante Dijkstra
    """
    min = sys.maxsize
    nodo_min = None
    for nodo in g.nodos:
        if not g.nodos[nodo].remove:
            if g.nodos[nodo].distancia_tentativa < min:
                min = g.nodos[nodo].distancia_tentativa
                nodo_min = nodo

    return nodo_min


def Dijkstra(g, origen, destino):
    """
    Implementacion clasica del Algoritmo de Dijkstra
    """

    #Establecemos la distancia tentativa del origen igual a 0
    g.nodos[origen].distancia_tentativa = 0

    #Diccionario en el que guardo los nodos y los padres de estos durante la busqueda
    prev = {origen:None}

    while(1):

        #Obtenemos el nodo con la menor distancia
        u = dist_min(g)

        if u == None:
            break #Significa que el nodo no tiene vecinos, por lo tanto devolvemos la cadena vacia como camino []

        #Marcamo el nodo con la menor distancia como removed
        g.nodos[u].remove = True

        "Caso de que lleguemos al nodo destino"
        if u == destino:
            S = [] #Lista que contrendra los nodos que constituyen el camino mas corto desde el Origen hasta el Destino
            u = destino
            
            if prev[u] is not None or u == origen:
                while u is not None:

                    S.insert(0, u)
                    u = prev[u]
            return S, prev
            
        for vecinos, distancia in g.nodos[u].vecinos:
            if not g.nodos[vecinos].remove:

                dist_tentativa = g.nodos[u].distancia_tentativa + distancia
               
                if dist_tentativa < g.nodos[vecinos].distancia_tentativa:
                    g.nodos[vecinos].distancia_tentativa = dist_tentativa
                    prev[vecinos] = u

    return [], []



"""***************************************************************************************************************************************************

                                                                      DIJKSTRA FRONTERAS                                                                          

"***************************************************************************************************************************************************"""

def Dijkstra_Frontera(g, origen, destino):
    """
    Implementacion clasica del Algoritmo de Dijkstra utilizando el concepto de fronteras, implementado mediante colas de prioridad
    """

    node = origen

    g.nodos[origen].distancia_tentativa = 0 #Coste

    frontera = PriorityQueue()
    frontera.put((0, node)) #Contiene al principio solo el nodo origen
    
    #Utilizo un set en el que voy guardando los nodos explorados duarante la busqueda
    explorado = set()

    #Diccionario en el que guardo los nodos y los padres de estos durante la busqueda
    solucion = {node: None}

    while frontera:
       
        if frontera.empty():
            return -1 #Return Fallo

        _, node = frontera.get()
        if node == destino:
            S = [] #Lista en la que guardo el camino mas corto

            if solucion[node] is not None or node == origen:
                while node is not None:
                    S.insert(0, node)
                    node = solucion[node]

            return S, solucion #Return Solucion
        
        explorado.add(node)

        for vecino, distancia in g.nodos[node].vecinos:
            if vecino not in explorado:

                coste_anterior = g.nodos[vecino].distancia_tentativa
                nuevo_coste = g.nodos[node].distancia_tentativa + distancia

                if nuevo_coste < coste_anterior:
                    frontera.put((nuevo_coste, vecino))
                    g.nodos[vecino].distancia_tentativa = nuevo_coste
                    solucion[vecino] = node




"""***************************************************************************************************************************************************

                                                                      A*                                                                          

"***************************************************************************************************************************************************"""

def dManhattan(g, nodo, destino):
    """"
    Funcion que calcula la heuristica de la Distancia de Manhattan
    """

    return abs(g.nodos[nodo].x - g.nodos[destino].x) + abs(g.nodos[nodo].y - g.nodos[destino].y)*3
    #Al multiplicar el valor de la heuristica por 2 o 3, reducimos las habitaciones que tiene que recorrer A* para llegar hasta el destino.
    #Como efecto tenemos que queda mas ovalada y dirigido hacia ese destino.



def A_ESTRELLA(g, origen, destino):
    """
    Implementacion del Algoritmo de Busqueda A* a partir de Dijkstra basado en fronteras
    """

    node = origen

    g.nodos[origen].distancia_tentativa = 0 #Coste

    frontera = PriorityQueue()
    frontera.put((0, node)) #Contiene al principio solo el nodo origen
    
    explorado = set()

    solucion = {node: None} #Parent

    while not frontera.empty():

        _, node = frontera.get()

        if node == destino:
            S = [] #Lista en la que guardo el camino mas corto
            if solucion[node] is not None or node == origen:
                while node is not None:
                    S.insert(0, node)
                    node = solucion[node]

            return S, solucion #Return Solucion
        
        explorado.add(node)

        for vecino, distancia in g.nodos[node].vecinos:
            if vecino not in explorado:

                coste_anterior = g.nodos[vecino].distancia_tentativa
                nuevo_coste = g.nodos[node].distancia_tentativa + distancia

                if nuevo_coste < coste_anterior:

                    #Establecemos la distancia tentativa del vecino 
                    g.nodos[vecino].distancia_tentativa = nuevo_coste

                    #Ahora guardamos en la cola, el nodo con el valor que toma de la funcion f(n) = d(n) + h(n), tomando como Heuristica la distancia de Manhattan
                    prioridad = nuevo_coste + dManhattan(g, vecino, destino)
                    frontera.put((prioridad, vecino))
                    
                    solucion[vecino] = node
            


def creaArray(filas, columnas, g):
    """
    Funcion que asocia a cada nodo/habitacion un valor entero.
    Empleo una valor "id" que servira como identificador de cada nodo.
    Tambien utilizo una matriz "array" de tamaño filas*columnas que inicializo a 0, en la que ire guardando los id's de los nodos.
    Utilizo 2 bucles for para iterar, y empleo la funcion "agregaNodo" de la clase Grafo para añadir un nuevo nodo en el grafo. Como comenté, tambien voy guardando en cada
    posicion de la matriz creada, el id de cada nodo.
    · Inputs:
        > filas: filas utilizadas para representar el laberinto en 2-dimensiones
        > columnas: columnas utilizadas para representar el laberinto en 2-dimensiones
        > g: Objeto de tipo grafo

    · Output:
        > array: matriz que contiene los distintos id's de los nodos que componen el grafo
    """
    id = 0
    array = np.zeros((filas, columnas))
    for i in range(filas):
        for c in range(columnas):
            g.agregaNodo(id)
            #Establecemos las x's y las y's de los nodos
            g.nodos[id].x = i
            g.nodos[id].y = c
            array[i][c] = id
            id += 1
    return array


def ide(matriz, f, c):
    """
    Funcion que retorna el id correspondiente a la habitacion indicada a partir de la fila y la columna
    · Inputs:
        > matriz: matriz que contiene los id's de los nodos que componen el grafo
        > f: valor de una fila de la matriz indicada previamente
        > c: valor de una columna de la matriz indicada previamente

    · Output:
        > Id correspondiente al nodo situado en las posiciones indicadas dentro de la matriz de id's
    """
    return matriz[f][c]


def generaLaberinto(filas, columnas, semilla, semilla2, pro, g):
    """
    Funcion que genera un laberinto a partir de una semilla
    · Inputs:
        > filas: filas utilizadas para representar el laberinto en 2-dimensiones
        > columnas: columnas utilizadas para representar el laberinto en 2-dimensiones
        > semilla: semilla utilizada para generar los ejes
        > semilla2: semilla utilizada para generar los pesos
        > pro: probabilidad empleada entre 0 y 1
        > g: Objeto de tipo grafo

    · Output:
        > array: matriz que contiene los distintos id's de los nodos que componen el grafo
    """

    #Creamos el array de nodos V
    array = creaArray(filas, columnas, g)

    #Inicializar rand-float con semilla
    random.seed(semilla)

    #Utilizamos una segunda semilla para generar los pesos
    random.seed(semilla2)


    for i in range (filas):
        for j in range(columnas):
            if i > 0 and semilla.rand() < pro:
                """
                Si se cumplen las condiciones, establecemos un eje entre el nodo en el que nos encontramos y el nodo que esta encima
                y viceversa (conmutatividad)
                """
                peso = int( semilla2.randi() % 12 + 1)
                #Agremamos los vecinos de cada nodo
                g.agregaEjes(int (ide(array,i,j)) , int (ide(array,i-1,j)), peso )

            if j > 0 and semilla.rand() < pro:
                """
                Si se cumplen las condiciones, establecemos un eje entre el nodo en el que nos encontramos y el nodo que esta a su izquierda
                y viceversa (conmutatividad)
                """
                #Agremamos los vecinos de cada nodo
                peso = int( semilla2.randi() % 12 + 1)
                g.agregaEjes(int (ide(array,i,j) ), int (ide(array,i,j-1)), peso )

    return array


def traspasarGrafo(filas, columnas, g, array, camino, camino_optimo, origen, destino):

    """
    Funcion que traspasa el grafo a una matriz para su dibujo con un mapa de calor.
    · Inputs:
        > filas: filas utilizadas para representar el laberinto en 2-dimensiones
        > columnas: columnas utilizadas para representar el laberinto en 2-dimensiones
        > g: Objeto de tipo grafo
        > array: matriz que contiene los distintos id's de los nodos que componen el grafo
        > camino: diccionario que contiene los nodos de la busqueda y sus respectivos padres, que se usara para pintar las distancias tentativas
        > camino_optimo: lista que contiene los nodos que conforman el camino más corto desde el origen hasta el destino
        > origen: nodo origen de la busqueda
        > destino: nodo destino de la busqueda

    · Output:
        > matrix: matriz de mapa de calor
    """

    #Inicializamos la matriz a -100 que representan las paredes
    matrix = np.full((filas*2+1, columnas*2+1), -100)

    for i in range(filas):
        for j in range(columnas):

            nodoActual = int(ide(array,i,j))
            if nodoActual in camino:

                if nodoActual in camino_optimo:
                    if nodoActual == origen or nodoActual == destino:
                        matrix[i*2+1][j*2+1] = 1000 #Origen y destino 
                    else:
                        matrix[i*2+1][j*2+1] = 800 #Resto de nodos que componen el camino mas corto
                else:
                    matrix[i*2+1][j*2+1] = g.nodos[nodoActual].distancia_tentativa

            
            else:
                matrix[i*2+1][j*2+1] = -1 #Habitacion que no se encuentra en el camino mas corto

        
            #Ponemos conexiones/pasillo hacia abajo y derecha
            lista_vecinos = []
            for vecinos in g.nodos[nodoActual].vecinos:
                lista_vecinos.append(vecinos[0])


            #Ponemos pasillos/conexiones hacia abajo y derecha
            if i < filas-1 and int(ide(array, i+1, j)) in lista_vecinos:

                if nodoActual in camino_optimo and int(ide(array, i+1, j)) in camino_optimo: #Si ambos estan en el camino optimo, pintamos el pasillo que los une del mismo color que los nodos

                        matrix[i*2+2][j*2+1] = 800

                else:
                    #Comprobar que el nodo de la derecha este en el camino porque sino su distancia tentativa no habra cambiado y sera el sys.maxsize
                    if int(ide(array, i+1, j)) in camino:

                        #El pasillo tendra el valor de la distancia tentativa mas pequeña de las 2 habitaciones que une
                        if g.nodos[nodoActual].distancia_tentativa < g.nodos[int(ide(array, i+1, j))].distancia_tentativa:
                            matrix[i*2+2][j*2+1] = g.nodos[nodoActual].distancia_tentativa
                        else:
                            matrix[i*2+2][j*2+1] = g.nodos[int(ide(array, i+1, j))].distancia_tentativa
                        
                    else:
                        #En el caso de que no este en el camino
                        matrix[i*2+2][j*2+1] = -1


            if j < columnas-1 and int(ide(array, i, j+1)) in lista_vecinos:

                if nodoActual in camino_optimo and int(ide(array, i, j+1)) in camino_optimo:
                    
                    matrix[i*2+1][j*2+2] = 800

                else:
                    #Comprobar que el nodo de debajo este en el camino porque sino su distancia tentativa no habra cambiado y sera el sys.maxsize
                    if int(ide(array, i, j+1)) in camino:

                        #El pasillo tendra el valor de la distancia tentativa mas pequeña de las 2 habitaciones que une
                        if g.nodos[nodoActual].distancia_tentativa < g.nodos[int(ide(array, i, j+1))].distancia_tentativa:
                            matrix[i*2+1][j*2+2] = g.nodos[nodoActual].distancia_tentativa
                        else:
                            matrix[i*2+1][j*2+2] = g.nodos[int(ide(array, i, j+1))].distancia_tentativa
                    
                    else:
                        #En el caso de que no este en el camino
                        matrix[i*2+1][j*2+2] = -1



    return matrix


"""
*******************************************************************************
                                    MAIN
*******************************************************************************
"""

def main():

    print("Implementacion lab 3.1 + 3.2")
    print()

    #Valores del array
    filas, columnas = 150,150
    s = 5
    s2 = 10
    s3 = 45
    semilla = SyncRNG(seed=s)
    semilla2 = SyncRNG(seed=s2)
    semilla3 = SyncRNG(seed=s3)

    #Probabilidad entre 0 y 1
    pro = 0.8

    g = Grafo()
    arrayIndNodos = generaLaberinto(filas, columnas, semilla, semilla2, pro, g)


    #Utilizamos una tercera semilla para el Origen y el Destino
    random.seed(semilla3)
    num_identificadores = 0
    for v in g.nodos:
        num_identificadores += 1

    
    origen_PRUEBAS = semilla3.randi() % num_identificadores
    destino_PRUEBAS = semilla3.randi() % num_identificadores

    print("origen:", origen_PRUEBAS)
    print("destino:", destino_PRUEBAS)

    #Procedemos a escoger la version deseada
    version = int(input("Escoge version: (1)Dijkstra basico  (2)Dijkstra Optimizado(Fronteras)  (3)A*: "))
    
    if version == 1:
        t0 = time.time()
        camino, preve = Dijkstra(g, origen_PRUEBAS, destino_PRUEBAS)
        t1 = time.time()
        print("Tiempos Dijsktra Clasico:", t1-t0)
        print("Camino mas corto:", camino)

        #Impresion valor ruta
        print("Valor total de la ruta: ", g.nodos[destino_PRUEBAS].distancia_tentativa)

        """
        Implementacion Dibujar laberintos mediante un mapa de calor
        """
        #Obtenemos la matriz de mapa de calor
        m = traspasarGrafo(filas, columnas, g, arrayIndNodos, preve, camino, origen_PRUEBAS, destino_PRUEBAS)
        plt.title("Dijkstra Clasico", fontsize=16)
    
    elif version == 2:
        t0 = time.time()
        camino2, preve2 = Dijkstra_Frontera(g, origen_PRUEBAS, destino_PRUEBAS)
        t1 = time.time()
        print("Tiempo Dijkstra Modificado:", t1-t0)
        print("Camino mas corto:", camino2)

        #Impresion valor ruta
        print("Valor total de la ruta: ", g.nodos[destino_PRUEBAS].distancia_tentativa)
        
        """
        Implementacion Dibujar laberintos mediante un mapa de calor
        """
        #Obtenemos la matriz de mapa de calor
        m = traspasarGrafo(filas, columnas, g, arrayIndNodos, preve2.keys(), camino2, origen_PRUEBAS, destino_PRUEBAS)
        plt.title("Dijkstra Fronteras", fontsize=16)

    
    else:
        t0 = time.time()
        optimo, camino_A_Estrella= A_ESTRELLA(g, origen_PRUEBAS, destino_PRUEBAS)
        t1 = time.time()
        print("Tiempo A*:", t1-t0)
        print("Camino mas corto", optimo)
        
        #Impresion 
        print("Valor total de la ruta: ", g.nodos[destino_PRUEBAS].distancia_tentativa)
        
        """
        Implementacion Dibujar laberintos mediante un mapa de calor
        """
        #Obtenemos la matriz de mapa de calor
        m = traspasarGrafo(filas, columnas, g, arrayIndNodos, camino_A_Estrella, optimo, origen_PRUEBAS, destino_PRUEBAS)
        plt.title("A*", fontsize=16)



    #Para conseguir que las paredes resalten con respecto a los otros valores introducidos por el recorrido hago lo siguiente:
    cmap=copy.copy(plt.get_cmap("hot"))
    cmap.set_under("gray")
    cmap.set_bad("blue")


    #Dibujar laberinto
    sb.heatmap(m,vmin=0,cmap=cmap,cbar_kws={'extend': 'min', 'extendrect': True}, annot=False, fmt="", mask=(m==-1))
    plt.show()


if __name__ == "__main__":
    main()