import AllCharacteristics.FundamentalCycle
import AllCharacteristics.CyclePushforward
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Cycles supplied by finite schemes and finite flat fibers

The degree is the dimension of the coordinate algebra, and finite flatness
preserves it under passage to residue-field fibers.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- The rank of a finite scheme over a field, computed from its actual ring of
global sections and structure morphism. -/
noncomputable def finiteSchemeRank
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] : ℕ :=
  let : IsAffine X := isAffine_of_isAffineHom f
  let a := (Spec.preimage (X.isoSpec.inv ≫ f)).hom
  let : Algebra k Γ(X, ⊤) := a.toAlgebra
  Module.finrank k Γ(X, ⊤)

/-- Every finite scheme over a field supplies an effective zero-cycle of its
rank. The proof constructs the affine fundamental cycle and transports it. -/
theorem exists_effectiveZeroCycle_degree_finiteSchemeRank
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsFinite f] :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = finiteSchemeRank f := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let A := Γ(X, ⊤)
  let g := X.isoSpec.inv ≫ f
  let a := Spec.preimage g
  let : Algebra k A := a.hom.toAlgebra
  have hg : Spec.map (CommRingCat.ofHom (algebraMap k A)) = g := Spec.map_preimage g
  have : IsFinite (Spec.map a) := by
    rw [Spec.map_preimage]
    infer_instance
  have : Module.Finite k A := (IsFinite.SpecMap_iff a).mp inferInstance
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finrank (k := k) (A := A)
  refine ⟨pushforwardClosedCycle X.isoSpec.inv z, ?_⟩
  rw [degree_pushforwardClosedCycle]
  have hz' : EffectiveZeroCycle.degree g z = Module.finrank k A := hg ▸ hz
  exact hz'

/-- A finite closed subscheme supplies an effective zero-cycle of the same rank
on its ambient scheme. -/
theorem exists_effectiveZeroCycle_of_finite_closed_subscheme
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsFinite (i ≫ f)] :
    ∃ z : EffectiveZeroCycle X,
      EffectiveZeroCycle.degree f z = finiteSchemeRank (i ≫ f) := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (i ≫ f)
  refine ⟨pushforwardClosedCycle i z, ?_⟩
  rw [degree_pushforwardClosedCycle]
  exact hz

/-- Each residue-field fiber of a finite flat algebra over a domain supplies an
effective cycle of the original rank, including nonreduced or inseparable fibers. -/
theorem exists_effectiveZeroCycle_finite_flat_fiber
    {R A : Type u} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A] (p : Ideal R) [p.IsPrime] :
    ∃ z : EffectiveZeroCycle (Spec (.of (p.Fiber A))),
      EffectiveZeroCycle.degree
        (Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField (p.Fiber A)))) z =
        Module.finrank R A := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finrank
    (k := p.ResidueField) (A := p.Fiber A)
  exact ⟨z, hz.trans (p.finrank_fiber_eq_finrank (M := A))⟩

/-- A cycle of degree prime to three contains a closed point of degree prime
to three. This includes the fundamental cycle of a nonreduced finite subscheme. -/
theorem EffectiveZeroCycle.exists_coprime_degree
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X)
    (h : Nat.Coprime (EffectiveZeroCycle.degree f z) 3) :
    ∃ x ∈ z.support, Nat.Coprime (f.residueDegree x.1) 3 := by
  have hn : ¬ 3 ∣ EffectiveZeroCycle.degree f z :=
    Nat.prime_three.coprime_iff_not_dvd.mp h.symm
  have hex : ∃ x ∈ z.support, ¬ 3 ∣ f.residueDegree x.1 := by
    by_contra hnone
    push Not at hnone
    apply hn
    exact Finset.dvd_sum (fun x hx ↦ dvd_mul_of_dvd_right (hnone x hx) (z x))
  obtain ⟨x, hx, hd⟩ := hex
  exact ⟨x, hx, (Nat.prime_three.coprime_iff_not_dvd.mpr hd).symm⟩

/-- A finite closed subscheme of rank prime to three and a degree-three cycle
supply a signed zero-cycle of degree one on the ambient scheme. -/
theorem degree_one_cycle_of_finite_closed_subscheme
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsFinite (i ≫ f)]
    (h : Nat.Coprime (finiteSchemeRank (i ≫ f)) 3)
    (z₃ : ZeroCycle X) (hz₃ : ZeroCycle.degree f z₃ = 3) :
    ∃ z : ZeroCycle X, ZeroCycle.degree f z = 1 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i f
  have hc : Nat.Coprime (EffectiveZeroCycle.degree f z) 3 := by rwa [hz]
  obtain ⟨x, _, hx⟩ := EffectiveZeroCycle.exists_coprime_degree f z hc
  exact ZeroCycle.exists_degree_one_of_coprime f z₃ hz₃ x hx

/-- A length-four finite closed subscheme yields a closed point of degree one,
two, or four, without a separability assumption. -/
theorem point_degree_one_two_four_of_finite_closed_subscheme
    {k : Type u} [Field k] {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of k)) [IsFinite (i ≫ f)]
    (h : finiteSchemeRank (i ≫ f) = 4) :
    ∃ x : closedPoints X,
      f.residueDegree x.1 = 1 ∨ f.residueDegree x.1 = 2 ∨ f.residueDegree x.1 = 4 := by
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_of_finite_closed_subscheme i f
  obtain ⟨x, _, hx⟩ := EffectiveZeroCycle.exists_degree_one_two_four f z (hz.trans h)
  exact ⟨x, hx⟩

end AllCharacteristics
