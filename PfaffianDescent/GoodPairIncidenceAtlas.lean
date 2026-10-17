import PfaffianDescent.GoodPairIncidenceFieldPoints
import PfaffianDescent.GoodPairMixedCartesian
import PfaffianDescent.SchemeDimensionFromCharts
import PfaffianDescent.PolynomialRelativeDimension

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
section
variable (K : Type u) [Field K] [CharZero K]

/-- The eight actual affine charts cover every point of the full first-two-form fiber. -/
theorem goodMixedPairCharts_cover (x : goodPairIncidenceFiber K) :
    ∃ ε : Fin 3 → Bool, ∃ y : goodMixedPairScheme K, goodMixedPairToGlobalFiber K ε y = x := by
  let L : Type u := (goodPairIncidenceFiber K).residueField x
  let z : Spec (.of L) ⟶ goodPairIncidenceFiber K := (goodPairIncidenceFiber K).fromSpecResidueField x
  let ψ : K →+* L := (Spec.preimage (z ≫ goodPairIncidenceFiberToBase K)).hom
  letI : Algebra K L := ψ.toAlgebra
  have hz : Spec.map (CommRingCat.ofHom (algebraMap K L)) = z ≫ goodPairIncidenceFiberToBase K :=
    Spec.map_preimage _
  let f : Spec (.of L) ⟶ incidenceScheme K :=
    z ≫ pullback.fst (incidenceToTriples K) (goodPairTripleSection K)
  have ht : f ≫ incidenceToTriples K =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ goodPairTripleSection K := by
    calc
      f ≫ incidenceToTriples K = z ≫
          (pullback.fst (incidenceToTriples K) (goodPairTripleSection K) ≫ incidenceToTriples K) :=
        Category.assoc _ _ _
      _ = z ≫ (goodPairIncidenceFiberToBase K ≫ goodPairTripleSection K) :=
        congrArg (fun t => z ≫ t) pullback.condition
      _ = (z ≫ goodPairIncidenceFiberToBase K) ≫ goodPairTripleSection K := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun t => t ≫ goodPairTripleSection K) hz.symm
  obtain ⟨ε, g, hg⟩ := goodPairIncidence_field_factor K f ht
  let hP := goodMixedPair_global_chart_isPullback K
    (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K) ≠ 0)) ε
  let q : Spec (.of L) ⟶ goodMixedPairScheme K := hP.lift z g hg.symm
  refine ⟨ε, q (IsLocalRing.closedPoint L), ?_⟩
  have hq : q ≫ goodMixedPairToGlobalFiber K ε = z := hP.lift_fst z g hg.symm
  exact (congrArg (fun t : Spec (.of L) ⟶ goodPairIncidenceFiber K => t (IsLocalRing.closedPoint L)) hq).trans
    ((goodPairIncidenceFiber K).fromSpecResidueField_apply x (IsLocalRing.closedPoint L))

/-- The complete eight-chart affine atlas of the scheme-theoretic first-two-form locus. -/
noncomputable def goodPairIncidenceOpenCover : Scheme.OpenCover.{u} (goodPairIncidenceFiber K) where
  I₀ := ULift.{u} (Fin 3 → Bool)
  X _ := goodMixedPairScheme K
  f ε := goodMixedPairToGlobalFiber K ε.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    constructor
    · intro x
      obtain ⟨ε, y, hy⟩ := goodMixedPairCharts_cover K x
      exact ⟨⟨ε⟩, y, hy⟩
    · intro ε
      exact goodMixedPairToGlobalFiber_open K
        (isUnit_iff_ne_zero.mpr (by norm_num : (2 : K) ≠ 0)) ε.down

lemma goodMixedPairToBase_relativeDimension : SmoothOfRelativeDimension 3 (goodMixedPairToBase K) := by
  change SmoothOfRelativeDimension 3
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 3) K))))
  simpa only [Nat.card_fin] using polynomial_smooth_relative_dimension K (Fin 3)

instance goodPairIncidenceFiberToBase_relativeDimension :
    SmoothOfRelativeDimension 3 (goodPairIncidenceFiberToBase K) := by
  let 𝒰 := goodPairIncidenceOpenCover K
  letI (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin 3) K))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 3) 𝒰
  intro i
  have hs : SmoothOfRelativeDimension 3 (𝒰.f i ≫ goodPairIncidenceFiberToBase K) := by
    change SmoothOfRelativeDimension 3 (goodMixedPairToGlobalFiber K i.down ≫ goodPairIncidenceFiberToBase K)
    rw [goodMixedPairToGlobalFiber_toBase]
    exact goodMixedPairToBase_relativeDimension K
  exact HasRingHomProperty.appTop _ _ hs

/-- The full first-two-form locus is a smooth three-dimensional proper scheme. -/
theorem goodPairIncidenceFiber_dimension : topologicalKrullDim (goodPairIncidenceFiber K) = 3 := by
  apply scheme_dimension_eq_of_openCover (goodPairIncidenceOpenCover K) ⟨fun _ => false⟩
  intro i
  change topologicalKrullDim (Spec (.of (MvPolynomial (Fin 3) K))) = 3
  rw [polynomialSpec_dimension, Nat.card_fin]
  norm_num

end
end PfaffianDescent
