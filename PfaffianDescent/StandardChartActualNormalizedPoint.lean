import PfaffianDescent.FiniteProjectiveStandardChartRestriction
import PfaffianDescent.CanonicalProjectiveFieldBaseChangeCharts

/-! Normalized points of all FOUR true chart algebras retain the original
embedding, on the ground scheme and on its actual field base change. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

def finiteProjectiveStandardChartAwayRestriction {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    HomogeneousLocalization.Away (homogeneousSubmodule (Fin 4) k) (X j) →+*
      Γ(finiteProjectiveStandardChart i j, ⊤) :=
  (finiteProjectiveStandardChartOpen i j).topIso.inv.hom.comp
    ((i.app (intrinsicQuadraticAmbientOpen (K := k) j).1).hom.comp
      (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j)).hom)

theorem finiteProjectiveStandardChartAwayRestriction_eq_normalized {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    finiteProjectiveStandardChartAwayRestriction i j =
      ambientNormalizedCoordinateChartMap
        (fun r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)) j
        (finiteProjectiveStandardChartPolynomialRestriction_coordinate_one i j) := by
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  apply RingHom.ext
  intro a
  obtain ⟨p, rfl⟩ := ambientChartEvaluation_surjective (R := k) j a
  rw [ambientNormalizedCoordinateChartMap_eval]
  change finiteProjectiveStandardChartPolynomialRestriction i j p = _
  have h := finiteProjectiveStandardChartPolynomialRestriction_eq_eval i j
  rw [finiteProjectiveStandardChartPolynomialRestriction_coefficients i j] at h
  exact DFunLike.congr_fun h p

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem finiteProjectiveStandardChartAwayRestriction_point {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartToBase_isFinite i j
    letI : IsAffine (finiteProjectiveStandardChart i j) :=
      isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
    Spec.map (CommRingCat.ofHom (finiteProjectiveStandardChartAwayRestriction i j)) ≫
      Proj.awayι (homogeneousSubmodule (Fin 4) k) (X j)
        (isHomogeneous_X k j) (by decide : 0 < 1) =
      (finiteProjectiveStandardChart i j).isoSpec.inv ≫
        (finiteProjectiveStandardChartOpen i j).ι ≫ i := by
  let U := intrinsicQuadraticAmbientOpen (K := k) j
  let V := finiteProjectiveStandardChartOpen i j
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  let t := finiteProjectiveStandardChartToBase i j
  letI : IsAffineHom t := (finiteProjectiveStandardChartToBase_isFinite i j).toIsAffineHom
  letI : IsAffine V := by
    change IsAffine (finiteProjectiveStandardChart i j)
    exact isAffine_of_isAffineHom t
  let hV : IsAffineOpen V := inferInstanceAs (IsAffine V)
  have hR : CommRingCat.ofHom (finiteProjectiveStandardChartAwayRestriction i j) =
      Proj.awayToSection (homogeneousSubmodule (Fin 4) k) (X j) ≫
        i.app U.1 ≫ V.topIso.inv := by
    apply CommRingCat.hom_ext
    rfl
  calc
    _ = Spec.map V.topIso.inv ≫ Spec.map (i.app U.1) ≫ U.2.fromSpec := by
      erw [hR, Spec.map_comp, Spec.map_comp]
      simp only [Category.assoc]
      rw [ambientCoordinateChart_fromSpec]
    _ = Spec.map V.topIso.inv ≫ hV.fromSpec ≫ i := by
      have hApp : Spec.map (i.app U.1) ≫ U.2.fromSpec = hV.fromSpec ≫ i := by
        rw [Scheme.Hom.app_eq_appLE]
        change Spec.map (i.appLE U.1 V le_rfl) ≫ U.2.fromSpec = _
        exact IsAffineOpen.SpecMap_appLE_fromSpec i U.2 hV le_rfl
      simpa only [Category.assoc] using congrArg (fun f => Spec.map V.topIso.inv ≫ f) hApp
    _ = _ := by
      simp only [IsAffineOpen.fromSpec, IsAffineOpen.isoSpec_inv, Category.assoc]
      change Spec.map V.topIso.inv ≫ Spec.map V.topIso.hom ≫
        V.toScheme.isoSpec.inv ≫ V.ι ≫ i = _
      rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
      rfl

/-- This point is built from the actual chart evaluation, and equals the
original embedding on that chart. No coordinate comparison is supplied. -/
theorem finiteProjectiveStandardChart_normalizedPoint_eq_original {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartToBase_isFinite i j
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    letI : IsAffine (finiteProjectiveStandardChart i j) :=
      isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
    ambientNormalizedCoordinateChartPoint
      (fun r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)) j
      (finiteProjectiveStandardChartPolynomialRestriction_coordinate_one i j) =
    (finiteProjectiveStandardChart i j).isoSpec.inv ≫
      (finiteProjectiveStandardChartOpen i j).ι ≫ i := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : IsAffine (finiteProjectiveStandardChart i j) :=
    isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
  unfold ambientNormalizedCoordinateChartPoint
  rw [← finiteProjectiveStandardChartAwayRestriction_eq_normalized]
  exact finiteProjectiveStandardChartAwayRestriction_point i j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual canonical new embedding on each true base-changed chart is
EXACTLY the normalized point on its tensor algebra. Both defining squares
are derived from the actual original chart map and the ambient pullback. -/
theorem canonicalProjectiveFieldBaseChangeChartTensorIso_normalizedPoint {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    let x := fun r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)
    let hx := finiteProjectiveStandardChartPolynomialRestriction_coordinate_one i j
    (canonicalProjectiveFieldBaseChangeChartTensorIso (K := K) i j).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx) =
    (finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j).ι ≫
      canonicalProjectiveFieldBaseChangeEmbedding (K := K) i := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : IsAffine (finiteProjectiveStandardChart i j) :=
    isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
  let x := fun r => finiteProjectiveStandardChartPolynomialRestriction i j (X r)
  let hx := finiteProjectiveStandardChartPolynomialRestriction_coordinate_one i j
  let e := canonicalProjectiveFieldBaseChangeChartTensorIso (K := K) i j
  let q := canonicalProjectiveFieldBaseChangeEmbedding (K := K) i
  let V := finiteProjectiveStandardChartOpen q j
  apply (isPullback_ambientCoefficientMap (σ := Fin 4) (algebraMap k K)).hom_ext
  · change (e.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)) ≫
        ambientCoefficientMap (σ := Fin 4) (algebraMap k K) = _
    calc
      _ = e.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(finiteProjectiveStandardChart i j, ⊤) →ₐ[k]
            K ⊗[k] Γ(finiteProjectiveStandardChart i j, ⊤)).toRingHom) ≫
          ambientNormalizedCoordinateChartPoint x j hx := by
        rw [Category.assoc, ambientNormalizedCoordinateChartPoint_tensor_coefficients]
      _ = e.hom ≫ Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight : Γ(finiteProjectiveStandardChart i j, ⊤) →ₐ[k]
            K ⊗[k] Γ(finiteProjectiveStandardChart i j, ⊤)).toRingHom) ≫
          (finiteProjectiveStandardChart i j).isoSpec.inv ≫
          (finiteProjectiveStandardChartOpen i j).ι ≫ i := by
        rw [finiteProjectiveStandardChart_normalizedPoint_eq_original]
      _ = V.ι ≫ pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (i ≫ ambientToBase) ≫ i := by
        rw [canonicalProjectiveFieldBaseChangeChartTensorIso_toOriginal_assoc]
      _ = _ := by
        simpa only [Category.assoc] using congrArg (fun f => V.ι ≫ f)
          (canonicalProjectiveFieldBaseChangeEmbedding_toOriginal (K := K) i).symm
  · change (e.hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun r => (1 : K) ⊗ₜ[k] x r) j (tensor_coordinate_eq_one x j hx)) ≫
        ambientToBase = _
    rw [Category.assoc, ambientNormalizedCoordinateChartPoint_toBase,
      canonicalProjectiveFieldBaseChangeChartTensorIso_toField]
    simpa only [Category.assoc] using congrArg (fun f => V.ι ≫ f)
      (canonicalProjectiveFieldBaseChangeEmbedding_toField (K := K) i).symm

end PfaffianDescent
