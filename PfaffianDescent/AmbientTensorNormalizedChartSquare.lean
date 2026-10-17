import AllCharacteristics.AmbientProjectiveBaseChange
import AllCharacteristics.HomogeneousChartEvaluation
import PfaffianDescent.VoisinQuotientAmbientChart
import PfaffianDescent.IntrinsicFullQuadraticSystem
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! Exact normalized projective chart points after scalar extension.
Their coefficient-change square is proved from the actual chart evaluator,
without a scheme comparison certificate or a reduced-support construction. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k K A : Type u} [Field k] [Field K] [CommRing A]
  [Algebra k K] [Algebra k A]

/-- Actual evaluation on the ordinary projective coordinate chart. -/
def ambientNormalizedCoordinateChartMap
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1) :
    Away (homogeneousSubmodule (Fin 4) F) (X j) →+* B :=
  AllCharacteristics.GradedChart.liftCoordinateOne
    (homogeneousSubmodule (Fin 4) F) (X j)
    (eval₂Hom (algebraMap F B) x) (by simpa only [eval₂Hom_X'] using hx)

theorem ambientNormalizedCoordinateChartMap_base
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1) (c : F) :
    ambientNormalizedCoordinateChartMap x j hx
      (AllCharacteristics.GradedChart.baseMap
        (homogeneousSubmodule (Fin 4) F) (z := X j) c) = algebraMap F B c := by
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap
    (homogeneousSubmodule (Fin 4) F) (X j)
    (eval₂Hom (algebraMap F B) x) _ c).trans (eval₂_C _ _ c)

theorem ambientNormalizedCoordinateChartMap_coordinate
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1) (r : Fin 4) :
    ambientNormalizedCoordinateChartMap x j hx
      (ambientChartCoordinate (R := F) j r) = x r := by
  exact (AllCharacteristics.GradedChart.liftCoordinateOne_normalized
    (homogeneousSubmodule (Fin 4) F) (X j)
    (eval₂Hom (algebraMap F B) x) _
    (isHomogeneous_X F j) (X r) (isHomogeneous_X F r)).trans (eval₂_X _ _ r)

theorem ambientNormalizedCoordinateChartMap_eval
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1)
    (p : MvPolynomial (Fin 4) F) :
    ambientNormalizedCoordinateChartMap x j hx (ambientChartEvaluation j p) =
      aeval (R := F) x p := by
  let h := ambientNormalizedCoordinateChartMap (F := F) x j hx
  have he : h.comp (ambientChartEvaluation j) = (aeval (R := F) x).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change h (ambientChartEvaluation j (C c)) = (aeval (R := F) x) (C c)
      rw [aeval_C]
      simpa only [h, ambientChartEvaluation, eval₂Hom_C] using
        ambientNormalizedCoordinateChartMap_base (F := F) x j hx c
    · intro r
      change h (ambientChartEvaluation j (X r)) = (aeval (R := F) x) (X r)
      rw [aeval_X]
      simpa only [h, ambientChartEvaluation, eval₂Hom_X'] using
        ambientNormalizedCoordinateChartMap_coordinate (F := F) x j hx r
  exact DFunLike.congr_fun he p

/-- This is an actual ambient projective morphism, built from its chart. -/
def ambientNormalizedCoordinateChartPoint
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1) :
    Spec (.of B) ⟶ Proj (homogeneousSubmodule (Fin 4) F) :=
  Spec.map (CommRingCat.ofHom (ambientNormalizedCoordinateChartMap x j hx)) ≫
    Proj.awayι (homogeneousSubmodule (Fin 4) F) (X j)
      (isHomogeneous_X F j) (by decide : 0 < 1)

theorem ambientNormalizedCoordinateChartPoint_toBase
    {F B : Type u} [Field F] [CommRing B] [Algebra F B]
    (x : Fin 4 → B) (j : Fin 4) (hx : x j = 1) :
    ambientNormalizedCoordinateChartPoint x j hx ≫ ambientToBase (R := F) =
      Spec.map (CommRingCat.ofHom (algebraMap F B)) := by
  unfold ambientNormalizedCoordinateChartPoint
  rw [Category.assoc, ambientCoordinateChart_toBase, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  apply congrArg (fun h => Spec.map (CommRingCat.ofHom h))
  exact RingHom.ext (ambientNormalizedCoordinateChartMap_base x j hx)

theorem tensor_coordinate_eq_one (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    (1 : K) ⊗ₜ[k] x j = (1 : K ⊗[k] A) := by rw [hx]; rfl

/-- The tensor chart map's square with the ORIGINAL coefficient chart map. -/
theorem ambientNormalizedCoordinateChartMap_tensor_coefficients
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    (ambientNormalizedCoordinateChartMap
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)).comp
        (ambientCoefficientChartMap (algebraMap k K) j) =
      (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom.comp
        (ambientNormalizedCoordinateChartMap x j hx) := by
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := k) j a
  change ambientNormalizedCoordinateChartMap (F := K)
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)
      (ambientCoefficientChartMap (algebraMap k K) j (ambientChartEvaluation j p)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
      (ambientNormalizedCoordinateChartMap (F := k) x j hx (ambientChartEvaluation j p))
  rw [ambientCoefficientChartMap_eval, ambientNormalizedCoordinateChartMap_eval]
  change aeval (R := K) (fun r => (1 : K) ⊗ₜ[k] x r)
      (p.map (algebraMap k K)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
      (ambientNormalizedCoordinateChartMap x j hx (ambientChartEvaluation j p))
  rw [ambientNormalizedCoordinateChartMap_eval, aeval_def, eval₂_map,
    ← IsScalarTower.algebraMap_eq k K (K ⊗[k] A)]
  change aeval (R := k) (fun r => (1 : K) ⊗ₜ[k] x r) p =
    (1 : K) ⊗ₜ[k] aeval (R := k) x p
  rw [MvPolynomial.aeval_one_tmul]

/-- Exact equality of actual projective morphisms after forgetting the
extension field. All algebra elements and nilpotent equations are retained. -/
theorem ambientNormalizedCoordinateChartPoint_tensor_coefficients
    (x : Fin 4 → A) (j : Fin 4) (hx : x j = 1) :
    ambientNormalizedCoordinateChartPoint
      (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx) ≫
        ambientCoefficientMap (algebraMap k K) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) ≫
          ambientNormalizedCoordinateChartPoint x j hx := by
  unfold ambientNormalizedCoordinateChartPoint
  rw [Category.assoc, awayι_comp_ambientCoefficientMap,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ambientNormalizedCoordinateChartMap_tensor_coefficients,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

/-- The normalized original point equals its real quotient chart point. -/
theorem ambientNormalizedCoordinateChartPoint_eq_original_chart
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (j : Fin 4) (g : ChartRing I j →+* A)
    (hbase : g.comp (chartBaseMap I j) = algebraMap k A) :
    ambientNormalizedCoordinateChartPoint
      (fun r => g (chartCoordinate I j r)) j
        (by rw [chartCoordinate_self, map_one]) =
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
  let x : Fin 4 → A := fun r => g (chartCoordinate I j r)
  have hx : x j = 1 := by simp only [x, chartCoordinate_self, map_one]
  have hmap : ambientNormalizedCoordinateChartMap x j hx =
      g.comp (quotientAmbientChartMap I j) := by
    apply RingHom.ext
    intro a
    obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := k) j a
    rw [ambientNormalizedCoordinateChartMap_eval]
    let evI := eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
    have hq : (quotientAmbientChartMap I j).comp (ambientChartEvaluation j) = evI := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simpa only [RingHom.comp_apply, ambientChartEvaluation, evI, eval₂Hom_C] using
          quotientAmbientChartMap_baseMap I j c
      · intro r
        simpa only [RingHom.comp_apply, ambientChartEvaluation, evI,
          eval₂Hom_X', ambientChartCoordinate] using
          quotientAmbientChartMap_coordinate I j r
    change p.eval₂ (algebraMap k A) x =
      g (((quotientAmbientChartMap I j).comp (ambientChartEvaluation j)) p)
    rw [hq]
    change p.eval₂ (algebraMap k A) x = g (p.eval₂ (chartBaseMap I j) (chartCoordinate I j))
    rw [hom_eval₂, hbase]
  change ambientNormalizedCoordinateChartPoint x j hx = _
  unfold ambientNormalizedCoordinateChartPoint
  rw [hmap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    ← chartι_comp_quotientProjMap]

/-- Apply scalar extension to whichever ORIGINAL chart has already been
selected by actual supplied-Z extraction. Thus callers retain the same
g/x used to calculate their residue basis and tangent matrix. -/
theorem ambientNormalizedTensorChartPoint_eq_original_chart
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (j : Fin 4) (g : ChartRing I j →+* A)
    (hbase : g.comp (chartBaseMap I j) = algebraMap k A) :
    ambientNormalizedCoordinateChartPoint
      (fun r => (1 : K) ⊗ₜ[k] g (chartCoordinate I j r)) j
        (tensor_coordinate_eq_one (fun r => g (chartCoordinate I j r)) j
          (by rw [chartCoordinate_self, map_one])) ≫
      ambientCoefficientMap (algebraMap k K) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) ≫
        Spec.map (CommRingCat.ofHom g) ≫ chartι I j ≫ quotientProjMap I := by
  rw [ambientNormalizedCoordinateChartPoint_tensor_coefficients
    (fun r => g (chartCoordinate I j r)) j (by rw [chartCoordinate_self, map_one]),
    ambientNormalizedCoordinateChartPoint_eq_original_chart I j g hbase]

end PfaffianDescent
