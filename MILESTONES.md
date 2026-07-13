# Milestones

## lean-2d-yang-mills — sandbox exactamente soluble

- M0: **cerrado para el modelo concreto SU(2)**. Heat kernel
  `K_t(g)=Σ_n (n+1)χ_n(g)e^{-t n(n+2)/4}`, puente Haar--esfera, ley orbital a
  todos los órdenes, convolución traducida de caracteres y semigrupo infinito.
- M1: **cerrado para la amplitud reducida de toda celulación finita orientada
  con dual conexo**. `exists_schedule_of_connected_graph` construye un
  calendario incluso con ciclos duales; `amplitude_eq_of_valid_schedules`
  prueba independencia de la elección; y la amplitud pública oculta el
  calendario. Queda abierta la equivalencia medida-preservante con la integral
  no reducida sobre todas las aristas de una celulación cíclica.
- M2: **cerrado mediante una instancia física no trivial para esa amplitud**.
  `su2ConnectedDiskExactAreaLawPackage` y su consumer prueban el exponencial de
  Casimir para todo label y toda celulación conectada de áreas positivas. No
  debe confundirse con la cota previa de acoplamiento fuerte del repositorio
  madre ni con una equivalencia todavía no probada al modelo de aristas sin
  gauge fixing.
- M3: statements-first del límite continuo (Lévy; Sengupta; Driver 1989).
- M4: zeta de Witten ζ_G(s)=Σ_λ dim(λ)^{-s}: convergencia y su papel en la
  función de partición sobre superficies.
