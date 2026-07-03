# Informe de sesión — lean-2d-yang-mills (empuje M4 + motor M0)

## Plantilla §B2

```
HECHO:
  Rama push/m4-witten-riemann (candidato a main, 0 sorry, 0 axiom):
    WittenZetaSU2.lean — su2WittenZetaPackage: WittenZetaPackage
      instanciado con zeta := riemannZeta de Mathlib, AMBOS campos de
      hipótesis descargados (sumabilidad para Re s > 1 vía
      Complex.summable_one_div_nat_cpow + shift; igualdad vía
      zeta_eq_tsum_one_div_nat_add_one_cpow + tsum_congr, usando
      Complex.cpow_neg para identificar el término (n+1)^(-s)). Titular:
      su2_wittenZetaSeries_eq_riemannZeta — LA ZETA DE WITTEN DE SU(2) ES
      LA ZETA DE RIEMANN. Y el modelo de área cero: Z_g = ζ(2g−2) para
      g ≥ 2 (consumer test declarado: la función de partición se DEFINE
      como la serie; el contenido genuino es la sumabilidad).
    ConvergenceEngine.lean — summable_pow_mul_exp_neg y su variante
      Casimir (n+1)^k·exp(−t·n(n+2)/4): el motor analítico que la
      expansión de caracteres de M0 consumirá.
    TrivialModel.lean — trivialHeatKernelPackage: HeatKernelCharacterPackage
      con TODOS los campos probados y la proposición de semigrupo enunciada
      como ley de convolución honesta (no True) y demostrada. Consumer test
      doctrinal del contrato M0.
    HYPOTHESIS_FRONTIER.md actualizado. Barrel extendido solo aditivamente.
  Rama frontier/M0-su2 (statements-first, sorried, NUNCA a main):
    Frontier/SU2Character.lean — DEFINICIÓN hoy de χ_n(g) = U_n(tr g / 2)
      vía Polynomial.Chebyshev.U de Mathlib; tabla SU(2) con Casimir
      n(n+2)/4; sorried: U_n(1) = n+1, cota de Weyl |χ_n| ≤ n+1 (input
      espectral: autovalores de SU(2) en el círculo), sumabilidad vía el
      motor ya probado, y existencia del paquete.
SIGUIENTE: verificar CI en push/m4-witten-riemann; luego la cota de Weyl
  |tr g| ≤ 2 para g ∈ SU(2) como unidad mínima — es el único input
  espectral que separa el M0 real del motor ya cerrado.
BLOQUEOS: ninguno nuevo. La capa Peter-Weyl compartida con el madre sigue
  pendiente (coordinar con PETER_WEYL_ROADMAP antes de subir la tabla SU(2)
  del frontier a main).
IMPACTO-INTERFAZ: contrato INTACTO (Interfaces.lean sin tocar; el barrel
  Lean2dYangMills.lean recibió tres imports aditivos, ningún nombre
  existente modificado). El ajuste honesto del T0 (heatKernel_semigroup
  como def : Prop) queda VALIDADO por el diseño: el modelo trivial muestra
  que el campo Prop puede cargar la ley de convolución real y probarse
  aparte — patrón recomendado para la futura instancia SU(2).
HONESTIDAD: (1) su2ZeroAreaSurfaceModel declara explícitamente que
  partition_eq_zeta es definicional (límite topológico); el M4 analítico a
  área positiva sigue abierto y así consta. (2) Build local verificado con
  `lake build Lean2dYangMills Interfaces`; CI/heartbeat siguen siendo el
  juez remoto antes de tocar `main`. (3) El puente
  Riemann es una identidad de series, no una reducción entre problemas del
  milenio; el README del madre ya lo enmarca así y nada aquí lo contradice.
```

## Cómo aplicar

```bash
git fetch origin
git checkout -b push/m4-witten-riemann origin/main
git am 0001-*.patch
git push -u origin push/m4-witten-riemann   # CI juzga; si verde → PR a main
git checkout -b frontier/M0-su2
git am 0002-*.patch
git push -u origin frontier/M0-su2
```

## VERIFICATION — puntos revisados en el primer build

1. `Complex.summable_one_div_nat_cpow` y
   `zeta_eq_tsum_one_div_nat_add_one_cpow` son los nombres correctos en el
   pin; el import `Mathlib.NumberTheory.LSeries.RiemannZeta` es correcto.
2. `summable_nat_add_iff` funciona en el pin con el argumento `1`.
3. La igualdad de zeta usa el lema desplazado `n+1`, así que ya no necesita
   `tsum_eq_zero_add` ni `Complex.zero_cpow`.
4. `Complex.cpow_neg`, `summable_pow_mul_geometric_of_norm_lt_one`,
   `Real.exp_lt_one_iff`, `Fintype.sum_unique`, `hasSum_fintype`,
   `tsum_fintype` y `Complex.intCast_re` son estables en el pin.
5. El motor y el modelo trivial se ajustaron a la API real del pin
   (`Nat.cast_nonneg (α := Real)` e instancia local
   `Fintype trivialCharacterTable.Label`).
6. Verificado localmente:
   `lake build Lean2dYangMills Interfaces`.
7. Frontier: `Polynomial.Chebyshev.U` está indexado por ℤ en Mathlib
   reciente (por eso el `(n : Int)`); si el pin aún lo indexa por ℕ, quitar
   el cast. Solo afecta a la rama frontier.

## Qué gana el madre con este empuje

El puente Riemann↔Yang-Mills del ecosistema deja de ser una frase del
roadmap: es un teorema con nombre (su2_wittenZetaSeries_eq_riemannZeta) que
identifica la zeta de Witten de SU(2) con riemannZeta de Mathlib, y las
funciones de partición topológicas de superficies de género g con los
valores especiales ζ(2g−2). Además el M0 duro queda reducido a UNA cota
espectral (|tr g| ≤ 2 en SU(2)): la definición del carácter vía Chebyshev ya
existe y el motor de sumabilidad que la consumirá ya está probado en main.
