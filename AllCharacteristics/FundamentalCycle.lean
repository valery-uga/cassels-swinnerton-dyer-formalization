import AllCharacteristics.FiniteAlgebraDegree
import AllCharacteristics.SchemeDegreeComparison
import AllCharacteristics.CycleDegrees

/-!
# Fundamental zero-cycles of finite schemes

The coefficient of a closed point is the length of the actual scheme stalk.
For a finite algebra over a field, the degree of this cycle is its dimension.
-/

open scoped BigOperators
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u

/-- The fundamental zero-cycle of an Artinian scheme, with local lengths as
multiplicities. -/
noncomputable def fundamentalZeroCycle (X : Scheme.{u}) [IsArtinianScheme X] :
    EffectiveZeroCycle X :=
  Finsupp.equivFunOnFinite.symm fun x : closedPoints X ↦
    (Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1)).toNat

@[simp] theorem fundamentalZeroCycle_apply
    (X : Scheme.{u}) [IsArtinianScheme X] (x : closedPoints X) :
    fundamentalZeroCycle X x =
      (Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1)).toNat := rfl

/-- Computing the degree of the intrinsic fundamental cycle as a finite sum. -/
theorem fundamentalZeroCycle_degree_eq_sum
    {X Y : Scheme.{u}} [IsArtinianScheme X] [Fintype (closedPoints X)] (f : X ⟶ Y) :
    EffectiveZeroCycle.degree f (fundamentalZeroCycle X) =
      ∑ x : closedPoints X,
        (Module.length (X.presheaf.stalk x.1) (X.presheaf.stalk x.1)).toNat *
          f.residueDegree x.1 := by
  exact Finsupp.sum_fintype _ _ (fun _ ↦ Nat.zero_mul _)

/-- A finite affine scheme's fundamental cycle has degree equal to its algebra
rank. The local multiplicities and the residue degrees are scheme-theoretic. -/
theorem fundamentalZeroCycle_degree_affine
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    [Module.Finite k A] [IsArtinianRing A] :
    EffectiveZeroCycle.degree (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (fundamentalZeroCycle (Spec (.of A))) = Module.finrank k A := by
  classical
  have : DiscreteTopology (Spec (.of A)) :=
    inferInstanceAs (DiscreteTopology (PrimeSpectrum A))
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let : Fintype (closedPoints (Spec (.of A))) := Fintype.ofFinite _
  let e : closedPoints (Spec (.of A)) ≃ PrimeSpectrum A :=
    Equiv.subtypeUnivEquiv (fun _ ↦ isClosed_singleton)
  rw [fundamentalZeroCycle_degree_eq_sum]
  calc
    _ = ∑ x : closedPoints (Spec (.of A)),
        (Module.length (Localization.AtPrime (e x).asIdeal)
          (Localization.AtPrime (e x).asIdeal)).toNat * Module.finrank k (e x).asIdeal.ResidueField := by
      apply Finset.sum_congr rfl
      intro x _
      exact congrArg₂ Nat.mul
        (congrArg ENat.toNat (affine_stalk_length_eq (.of A) (e x)))
        (affine_residueDegree_eq_finrank (e x))
    _ = ∑ q : PrimeSpectrum A,
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat * Module.finrank k q.asIdeal.ResidueField :=
      e.sum_comp (fun q : PrimeSpectrum A ↦
        (Module.length (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)).toNat * Module.finrank k q.asIdeal.ResidueField)
    _ = Module.finrank k A := (finrank_eq_sum_local_length_mul_residue_degree k A).symm

/-- A finite algebra supplies an actual effective zero-cycle of its rank on its
spectrum. Artinianness follows from finiteness over the field. -/
theorem exists_effectiveZeroCycle_degree_finrank
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] :
    ∃ z : EffectiveZeroCycle (Spec (.of A)),
      EffectiveZeroCycle.degree (Spec.map (CommRingCat.ofHom (algebraMap k A))) z =
        Module.finrank k A := by
  have : IsArtinianRing A := isArtinian_of_tower k inferInstance
  exact ⟨fundamentalZeroCycle (Spec (.of A)), fundamentalZeroCycle_degree_affine⟩

end AllCharacteristics
