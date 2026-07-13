# Milestones

## lean-2d-yang-mills — sandbox exactamente soluble

- M0: **cerrado para el modelo concreto SU(2)**. Heat kernel
  `K_t(g)=Σ_n (n+1)χ_n(g)e^{-t n(n+2)/4}`, puente Haar--esfera, ley orbital a
  todos los órdenes, convolución traducida de caracteres y semigrupo infinito.
- M1: **cerrado globalmente para discos poligonales de dual arbóreo**.
  `su2PlanarCellulationAmplitude_eq_heatKernel` integra recursivamente todas
  las aristas internas, prueba terminación con `E=F-1` y produce una cara
  efectiva. Quedan abiertos los mapas planares con ciclos duales/interior
  vertices y la independencia de la elección de gauge fixing.
- M2: **cerrado mediante una instancia física no trivial para esa clase**.
  `su2TreePlanarExactAreaLawPackage` y su consumer prueban el exponencial de
  Casimir para todo label, toda área positiva y toda celulación del tipo. No
  debe confundirse con la cota previa de acoplamiento fuerte del repositorio
  madre.
- M3: statements-first del límite continuo (Lévy; Sengupta; Driver 1989).
- M4: zeta de Witten ζ_G(s)=Σ_λ dim(λ)^{-s}: convergencia y su papel en la
  función de partición sobre superficies.
