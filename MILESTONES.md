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
  `exists_rootedTreeVertexCoordinateEquiv_measurePreserving` cierra una única
  transformación global Haar-preservante sobre todas las variables de vértice
  de una celulación primal-conexa. Queda abierta la equivalencia sobre todas
  las variables originales de arista y la identificación simultánea de las
  holonomías faciales.
- M2: **cerrado mediante una instancia física no trivial para esa amplitud**.
  `su2ConnectedDiskExactAreaLawPackage` y su consumer prueban el exponencial de
  Casimir para todo label y toda celulación conectada de áreas positivas. No
  debe confundirse con la cota previa de acoplamiento fuerte del repositorio
  madre; el puente al modelo de aristas sin gauge fixing está demostrado en el
  caso cíclico de tres caras, pero aún no uniformemente para toda celulación.
- M3: statements-first del límite continuo (Lévy; Sengupta; Driver 1989).
- M4: zeta de Witten ζ_G(s)=Σ_λ dim(λ)^{-s}: convergencia y su papel en la
  función de partición sobre superficies.
