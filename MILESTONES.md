# Milestones

## lean-2d-yang-mills — sandbox exactamente soluble

- M0: **cerrado para el modelo concreto SU(2)**. Heat kernel
  `K_t(g)=Σ_n (n+1)χ_n(g)e^{-t n(n+2)/4}`, puente Haar--esfera, ley orbital a
  todos los órdenes, convolución traducida de caracteres y semigrupo infinito.
- M1: **cerrado para la amplitud reducida de toda celulación finita orientada
  con dual conexo**. `exists_schedule_of_connected_graph` construye un
  calendario incluso con ciclos duales; `amplitude_eq_of_valid_schedules`
  prueba independencia de la elección; y la amplitud pública oculta el
  calendario. Para el primer ciclo no trivial, el disco de tres caras y tres
  radios, `su2ThreeSpoke_unreducedIntegral_eq_gaugeFixedIntegral` prueba además
  la equivalencia medida-preservante con la integral original de Haar producto.
  `su2FiniteStarGaugeFix_measurePreserving` y
  `su2FiniteStar_integral_eq_identitySlice` hacen uniforme el paso local para
  cualquier valencia finita. `exists_validForGraph_of_connected` construye un
  árbol generador ordenado para todo grafo finito conexo, y
  `exists_rootedTreeVertexCoordinateEquiv_measurePreserving` cierra la capa de
  vértices. `globalEdgeGaugeEquiv_measurePreserving` la eleva a todas las
  aristas originales, `allFaceHolonomies_gaugeTransform` da simultáneamente las
  holonomías faciales y
  `unreducedEdgeIntegral_eq_chordGaugeFixedIntegral` elimina exactamente las
  `V-1` coordenadas gauge de la integral Haar. El puente de aristas queda
  cerrado para toda celulación de disco conexa y facialmente bien formada.
- M2: **cerrado mediante una instancia física no trivial para esa amplitud**.
  `su2ConnectedDiskExactAreaLawPackage` y su consumer prueban el exponencial de
  Casimir para todo label y toda celulación conectada de áreas positivas. No
  debe confundirse con la cota previa de acoplamiento fuerte del repositorio
  madre; el puente al modelo de aristas sin gauge fixing es ahora uniforme en
  toda celulación de aristas bien formada.
- M3: statements-first del límite continuo (Lévy; Sengupta; Driver 1989).
- M4: zeta de Witten ζ_G(s)=Σ_λ dim(λ)^{-s}: convergencia y su papel en la
  función de partición sobre superficies.

## Siguientes frentes, sin desviar el cierre actual

1. `hRpoly`: volver a la cadena analítica dura solo después de congelar este
   release; el cuello de botella sigue siendo coercividad uniforme/localización
   del inverso, no infraestructura de celulaciones.
2. Surface Theorem: retomar el cierre de G1/G2 y colas como segundo frente
   coordinado. Ninguno de estos dos objetivos se usa como hipótesis del
   resultado bidimensional actual.
