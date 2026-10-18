import AllCharacteristics.KollarGenericResidual
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The generic line root is generic on the original affine cubic cone

An irreducible equation remains primitive when one coordinate is regarded as
the polynomial variable.  A root over the rational function field of all
other coordinates therefore has exactly that original equation as its
polynomial kernel.  This is a genericity theorem derived from actual root
coordinates, without assuming genericity or dominance.
-/

namespace AllCharacteristics

open AlgebraicGeometry HomogeneousProjective PfaffianDescent MvPolynomial Polynomial

universe u

variable {K : Type u} [Field K]

/-- Evaluate all cone coordinates at a distinguished polynomial root and
the remaining independent rational-function coordinates. -/
noncomputable def distinguishedRootConeEvaluation
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) L] (a : L) :
    MvPolynomial (Fin 4) K →+* L :=
  (Polynomial.aeval a).toRingHom.comp
    ((Polynomial.mapRingHom
      (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)))).comp
        (MvPolynomial.finSuccEquiv K 3).toRingHom)

/-- The distinguished cone coordinate is the chosen root. -/
theorem distinguishedRootConeEvaluation_X_zero
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) L] (a : L) :
    distinguishedRootConeEvaluation (K := K) a (MvPolynomial.X 0) = a := by
  simp [distinguishedRootConeEvaluation, MvPolynomial.finSuccEquiv_apply]

/-- The other cone coordinates remain independent generic direction
coordinates, viewed in the specified root field. -/
theorem distinguishedRootConeEvaluation_X_succ
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) L] (a : L) (j : Fin 3) :
    distinguishedRootConeEvaluation (K := K) a (MvPolynomial.X j.succ) =
      algebraMap (FractionRing (MvPolynomial (Fin 3) K)) L
        (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K))
          (MvPolynomial.X j)) := by
  simp [distinguishedRootConeEvaluation, MvPolynomial.finSuccEquiv_apply]

/-- A root of the distinguished polynomial over the generic direction field
has exactly the original cubic equation as its cone-coordinate kernel.
The degree hypothesis only excludes an equation independent of the
distinguished coordinate. -/
theorem distinguishedRootConeEvaluation_ker
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F)
    (hdegree : (MvPolynomial.finSuccEquiv K 3 F).natDegree ≠ 0)
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) L]
    (a : L)
    (ha : Polynomial.aeval a
      ((MvPolynomial.finSuccEquiv K 3 F).map
        (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)))) = 0) :
    RingHom.ker (distinguishedRootConeEvaluation (K := K) a) =
      Ideal.span ({F} : Set (MvPolynomial (Fin 4) K)) := by
  let R := MvPolynomial (Fin 3) K
  let Q := FractionRing R
  let e := MvPolynomial.finSuccEquiv K 3
  let P := e F
  have hPirr : Irreducible P := hF.map e.toRingEquiv
  have hPprimitive : P.IsPrimitive := hPirr.isPrimitive hdegree
  have hPmapirr : Irreducible (P.map (algebraMap R Q)) :=
    hPprimitive.irreducible_iff_irreducible_map_fraction_map.mp hPirr
  ext G
  change distinguishedRootConeEvaluation (K := K) a G = 0 ↔ G ∈ Ideal.span ({F} : Set _)
  change Polynomial.aeval a ((e G).map (algebraMap R Q)) = 0 ↔
    G ∈ Ideal.span ({F} : Set _)
  rw [hPmapirr.dvd_iff_aeval_eq_zero ha, Ideal.mem_span_singleton]
  constructor
  · intro hdiv
    have hd : P ∣ e G := hPprimitive.dvd_of_fraction_map_dvd_fraction_map hdiv
    obtain ⟨H, hH⟩ := hd
    refine ⟨e.symm H, ?_⟩
    apply e.injective
    rw [map_mul, e.apply_symm_apply]
    exact hH
  · intro hdiv
    exact map_dvd (Polynomial.mapRingHom (algebraMap R Q)) (map_dvd e.toRingHom hdiv)

/-- Every nonzero polynomial of degree at most two is nonzero at these actual
generic cubic cone coordinates.  Homogeneity of the test polynomial is not
required. -/
theorem distinguishedRootConeEvaluation_lowDegree_ne_zero
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hirr : Irreducible F)
    (hdegree : (MvPolynomial.finSuccEquiv K 3 F).natDegree ≠ 0)
    {L : Type u} [Field L]
    [Algebra (FractionRing (MvPolynomial (Fin 3) K)) L]
    (a : L)
    (ha : Polynomial.aeval a
      ((MvPolynomial.finSuccEquiv K 3 F).map
        (algebraMap (MvPolynomial (Fin 3) K) (FractionRing (MvPolynomial (Fin 3) K)))) = 0)
    (G : MvPolynomial (Fin 4) K) (hG : G ≠ 0) (hGdegree : G.totalDegree ≤ 2) :
    distinguishedRootConeEvaluation (K := K) a G ≠ 0 := by
  intro hzero
  have hmem : G ∈ RingHom.ker (distinguishedRootConeEvaluation (K := K) a) := hzero
  rw [distinguishedRootConeEvaluation_ker F hirr hdegree a ha] at hmem
  have hdvd : F ∣ G := Ideal.mem_span_singleton.mp hmem
  have hle := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hG
  rw [hF.totalDegree hirr.ne_zero] at hle
  omega

end AllCharacteristics
