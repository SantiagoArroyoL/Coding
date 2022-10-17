# -*- coding: utf-8 -*-
"""
Integrantes de equipo:

- Santiago Arroyo Lozano
- Jesús Israel Gutiérrez Elizalde
- Carlos Andrade Hernandez
- Ricardo Adrián Luévano Ballesteros
"""

def scheduling(lst):
    """ Algoritmo greedy para agendar la mayor cantidad de eventos
    cuyos horarios no se empalmen.
    
    :param lst: Lista de eventos, donde cada vento es una tupla 
                (hora inicial, hora final)
    
    :return:    La lista de eventos agendados.
    
    >>> scheduling([(1,3), (2,5), (3,9), (6,8)])
    [(1, 3), (6, 8)]
    """
    
    # Se ordena la lista con base en la hora final del evento.
    lst.sort(key = lambda x: x[1])  
    final = []
    for e in lst:
        # Se revisa si la lista es vacía.
        if(not final):              
            # Primer elemento siempre es el mejor.
            final.append(e)         
            continue
        # Hora final de último evento contra hora inicial del evento actual.
        if(final[-1][1] <= e[0]):   
            final.append(e)         
    return final

a = [(1,3), (2,5), (3,9), (6,8)]
print(scheduling(a))