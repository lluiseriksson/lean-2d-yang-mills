# Milestones

## lean-2d-yang-mills — sandbox exactamente soluble

- M0: SU(2); heat kernel K_t(g)=Σ_λ dim(λ)χ_λ(g)e^{-tC₂(λ)}.
  La tabla concreta, la cota de Weyl, la invariancia por conjugación y la
  convergencia uniforme, continuidad y la ortogonalidad angular de Weyl están cerradas.
  Haar normalizado ya se construye internamente y el selector de caracteres
  impares está probado. También están cerrados los momentos Haar exactos
  `E|g₀₀|²=1/2`, `E(Re g₀₀)²=1/4`, la normalización fundamental y el primer
  carácter par `∫χ₂=0`. Falta la fórmula de Weyl completa y la identidad
  matricial de convolución. La equivalencia y el homeomorfismo concretos
  `SU(2) ≃ S³` ya están cerrados. Haar ya se transporta a una probabilidad
  sobre la esfera y su invariancia bajo la acción SU(2) completa está probada;
  la esfera ya está homeomorfa al tipo L2 exacto de `volume.toSphere`, cuya
  medida canónica normalizada también está construida y devuelta al mismo
  tipo. Falta demostrar la igualdad literal de ambas medidas. Coordina con el
  PETER_WEYL_ROADMAP.
- M1: invariancia de la acción heat-kernel bajo subdivisión (Migdal).
- M2: Wilson loop exacto en el plano: área law con tensión explícita
  (benchmark del área law en volumen finito del madre).
- M3: statements-first del límite continuo (Lévy; Sengupta; Driver 1989).
- M4: zeta de Witten ζ_G(s)=Σ_λ dim(λ)^{-s}: convergencia y su papel en la
  función de partición sobre superficies.
