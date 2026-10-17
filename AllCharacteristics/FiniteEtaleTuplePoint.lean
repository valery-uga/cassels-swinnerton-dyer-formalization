import AllCharacteristics.ProjectiveFiniteEtaleConfiguration
import AllCharacteristics.HomogeneousConfigurationQuotient
import AllCharacteristics.ProjectiveBaseChange

/-!
# Finite étale subschemes as points of the full tuple quotient

The unordered distinct-configuration quotient is an open subscheme of the
full unordered-tuple quotient.  Thus the rational configuration point
attached to a finite étale subscheme also gives a rational tuple point.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u v

variable {R : Type u} [CommRing R] {σ : Type v} [SetLike σ R] [AddSubgroupClass σ R]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A finite étale rank-`n` subscheme of a projective family determines a
rational point of the full unordered-tuple quotient. -/
theorem exists_projectiveOrderedTupleQuotientPoint_of_finiteEtaleSubscheme
    {K : Type u} [Field K] [CharZero K]
    (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
    (n : ℕ) (D : FiniteSubschemeDatum f n)
    [Etale (D.val.subschemeι ≫ f)] :
    ∃ s : Spec (.of K) ⟶ projectiveOrderedTupleQuotient 𝒜 f n,
      s ≫ projectiveOrderedTupleQuotientToBase 𝒜 f n = 𝟙 _ := by
  obtain ⟨c, hc⟩ :=
    exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme
      𝒜 f n D
  refine ⟨c ≫ (projectiveConfigurationQuotientOpen 𝒜 f n).ι, ?_⟩
  rw [Category.assoc]
  exact hc

/-- A finite étale subscheme on a field-valued base change determines a
field-valued point of the original full unordered-tuple quotient. -/
theorem exists_projectiveOrderedTupleQuotientPoint_of_finiteEtaleSubscheme_baseChange
    {S X : Scheme.{u}} [IsAffine S]
    (f : Proj 𝒜 ⟶ S) [IsSeparated f]
    {K : Type u} [Field K] [CharZero K]
    (b : Spec (.of K) ⟶ S) (g : X ⟶ Proj 𝒜)
    (pX : X ⟶ Spec (.of K))
    (hpb : IsPullback g pX f b)
    (n : ℕ) (D : FiniteSubschemeDatum pX n)
    (hEt : Etale (D.val.subschemeι ≫ pX)) :
    ∃ s : Spec (.of K) ⟶ projectiveOrderedTupleQuotient 𝒜 f n,
      s ≫ projectiveOrderedTupleQuotientToBase 𝒜 f n = b := by
  obtain ⟨c, hc⟩ :=
    exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme_baseChange
      𝒜 f b g pX hpb n D hEt
  refine ⟨c ≫ (projectiveConfigurationQuotientOpen 𝒜 f n).ι, ?_⟩
  rw [Category.assoc]
  exact hc

namespace HomogeneousProjective

variable {K : Type u} [Field K] [CharZero K] {τ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ K))

/-- A finite étale rank-`n` subscheme of a homogeneous projective scheme
determines a rational point of its full unordered-tuple quotient. -/
theorem exists_tupleQuotientPoint_of_finiteEtaleSubscheme
    (n : ℕ) (D : FiniteSubschemeDatum (toBase I) n)
    [Etale (D.val.subschemeι ≫ toBase I)] :
    ∃ s : Spec (.of K) ⟶ tupleQuotient I n,
      s ≫ tupleQuotientToBase I n = 𝟙 _ := by
  have het : Etale (D.val.subschemeι ≫ toBase I) := inferInstance
  let f : Proj (grading I) ⟶ Spec (.of K) := toBase I
  letI : IsSeparated f := inferInstanceAs (IsSeparated (toBase I))
  let D' : FiniteSubschemeDatum f n := D
  letI : Etale (D'.val.subschemeι ≫ f) := by
    dsimp only [D', f]
    exact het
  exact exists_projectiveOrderedTupleQuotientPoint_of_finiteEtaleSubscheme
    (grading I) f n D'

/-- A finite étale subscheme on a coefficient-changed hypersurface gives a
point of the original hypersurface's full tuple quotient over the enlarged
coefficient field. -/
theorem exists_tupleQuotientPoint_of_finiteEtaleHypersurfaceCoefficientChange
    {L : Type u} [Field L] [CharZero L]
    (a : K →+* L) (p : MvPolynomial τ K) {d : ℕ}
    (hp : p.IsHomogeneous d) (n : ℕ)
    (D : FiniteSubschemeDatum
      (hypersurfaceToBase (p.map a) (hp.map a)) n)
    [Etale (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a) (hp.map a))] :
    ∃ s : Spec (.of L) ⟶ tupleQuotient (equationIdeal p hp) n,
      s ≫ tupleQuotientToBase (equationIdeal p hp) n =
        Spec.map (CommRingCat.ofHom a) := by
  have het : Etale (D.val.subschemeι ≫
      hypersurfaceToBase (p.map a) (hp.map a)) := inferInstance
  let I := equationIdeal p hp
  let J := equationIdeal (p.map a) (hp.map a)
  let h : I.toIdeal.map (MvPolynomial.map a) = J.toIdeal :=
    equationIdeal_map a p hp
  let f : Proj (grading I) ⟶ Spec (.of K) := toBase I
  letI : IsSeparated f := inferInstanceAs (IsSeparated (toBase I))
  let pX : Proj (grading J) ⟶ Spec (.of L) := toBase J
  let D' : FiniteSubschemeDatum pX n := D
  have hEt' : Etale (D'.val.subschemeι ≫ pX) := by
    dsimp only [D', pX, J]
    exact het
  exact
    exists_projectiveOrderedTupleQuotientPoint_of_finiteEtaleSubscheme_baseChange
      (grading I) f
      (Spec.map (CommRingCat.ofHom a))
      (projectiveCoefficientMap a I J h) pX
      (isPullback_projectiveCoefficientMap a I J h) n D' hEt'

end HomogeneousProjective
end AllCharacteristics
