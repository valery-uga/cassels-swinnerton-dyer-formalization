import PfaffianDescent.FiniteProjectiveStandardChartAlgebra
import PfaffianDescent.SingleSupportActualTensorAmbientSquare
import AllCharacteristics.AmbientProjectiveBaseChange

/-! The actual field-base-changed embedding and its FOUR actual chart
preimages. These are scheme Isos, retaining the original chart projection;
no radical ideal, global avoiding hyperplane, or comparison certificate is
used. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra

def canonicalProjectiveFieldBaseChangeEmbedding {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (i ≫ ambientToBase) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K) := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let t := i ≫ ambientToBase (R := k)
  refine (isPullback_ambientCoefficientMap (σ := Fin 4) (algebraMap k K)).lift
    (pullback.snd b t ≫ i) (pullback.fst b t) ?_
  simpa only [Category.assoc] using (pullback.condition (f := b) (g := t)).symm

@[reassoc]
theorem canonicalProjectiveFieldBaseChangeEmbedding_toOriginal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) :
    canonicalProjectiveFieldBaseChangeEmbedding (K := K) i ≫
      ambientCoefficientMap (σ := Fin 4) (algebraMap k K) =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (i ≫ ambientToBase) ≫ i := by
  unfold canonicalProjectiveFieldBaseChangeEmbedding
  apply IsPullback.lift_fst

@[reassoc]
theorem canonicalProjectiveFieldBaseChangeEmbedding_toField {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) :
    canonicalProjectiveFieldBaseChangeEmbedding (K := K) i ≫ ambientToBase =
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (i ≫ ambientToBase) := by
  unfold canonicalProjectiveFieldBaseChangeEmbedding
  apply IsPullback.lift_snd

theorem canonicalProjectiveFieldBaseChangeEmbedding_isPullback {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) :
    IsPullback (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i)
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ ambientToBase))
      (ambientCoefficientMap (σ := Fin 4) (algebraMap k K)) i := by
  unfold canonicalProjectiveFieldBaseChangeEmbedding
  exact (IsPullback.of_bot'
    (IsPullback.of_hasPullback
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ ambientToBase)).flip
    (isPullback_ambientCoefficientMap (σ := Fin 4) (algebraMap k K))).flip

theorem canonicalProjectiveFieldBaseChangeEmbedding_isClosedImmersion {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsClosedImmersion i] :
    IsClosedImmersion (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) := by
  exact MorphismProperty.of_isPullback
    (canonicalProjectiveFieldBaseChangeEmbedding_isPullback (K := K) i).flip
    (inferInstance : IsClosedImmersion i)

theorem canonicalProjectiveFieldBaseChangeEmbedding_isFinite {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] :
    IsFinite (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i ≫ ambientToBase) := by
  rw [canonicalProjectiveFieldBaseChangeEmbedding_toField]
  infer_instance

theorem canonicalProjectiveFieldBaseChangeEmbedding_chart_preimage {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (i ≫ ambientToBase) ⁻¹ᵁ finiteProjectiveStandardChartOpen i j := by
  let q := canonicalProjectiveFieldBaseChangeEmbedding (K := K) i
  let a := ambientCoefficientMap (σ := Fin 4) (algebraMap k K)
  let p := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (i ≫ ambientToBase (R := k))
  let U := (intrinsicQuadraticAmbientOpen (K := k) j).1
  have hU : a ⁻¹ᵁ U = (intrinsicQuadraticAmbientOpen (K := K) j).1 :=
    ambientCoefficientMap_preimage_coordinate (algebraMap k K) j
  change q ⁻¹ᵁ (intrinsicQuadraticAmbientOpen (K := K) j).1 = p ⁻¹ᵁ (i ⁻¹ᵁ U)
  rw [← hU, ← Scheme.Hom.comp_preimage,
    canonicalProjectiveFieldBaseChangeEmbedding_toOriginal, Scheme.Hom.comp_preimage]

/-- Any actual open part of a finite scheme commutes with field base change
as a Cartesian square. The open is not required to be a principal chart. -/
theorem finiteSchemeFieldBaseChange_open_isPullback {Z : Scheme.{u}}
    (t : Z ⟶ Spec (.of k)) (V : Z.Opens) :
    let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
    let p := pullback.snd b t
    IsPullback ((p ⁻¹ᵁ V).ι ≫ pullback.fst b t) (p ∣_ V) b (V.ι ≫ t) := by
  dsimp only
  exact (isPullback_morphismRestrict _ V).flip.paste_horiz
    (IsPullback.of_hasPullback _ _)

def canonicalProjectiveFieldBaseChangeChartIso {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    finiteProjectiveStandardChart (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (finiteProjectiveStandardChartToBase i j) := by
  let t := i ≫ ambientToBase (R := k)
  let V := finiteProjectiveStandardChartOpen i j
  exact (pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) t).isoOfEq
      (canonicalProjectiveFieldBaseChangeEmbedding_chart_preimage (K := K) i j) ≪≫
    (finiteSchemeFieldBaseChange_open_isPullback (K := K) t V).isoPullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual new chart remains above the SAME original subscheme, not
just an abstract tensor algebra with the right dimension. -/
@[reassoc]
theorem canonicalProjectiveFieldBaseChangeChartIso_toOriginal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    (canonicalProjectiveFieldBaseChangeChartIso (K := K) i j).hom ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (finiteProjectiveStandardChartToBase i j) ≫
      (finiteProjectiveStandardChartOpen i j).ι =
    (finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j).ι ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ ambientToBase) := by
  dsimp only [canonicalProjectiveFieldBaseChangeChartIso, Iso.trans_hom,
    finiteProjectiveStandardChartToBase]
  simp only [Category.assoc, IsPullback.isoPullback_hom_snd_assoc,
    morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem canonicalProjectiveFieldBaseChangeChartIso_toField {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k)) (j : Fin 4) :
    (canonicalProjectiveFieldBaseChangeChartIso (K := K) i j).hom ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (finiteProjectiveStandardChartToBase i j) =
    (finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j).ι ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ ambientToBase) := by
  dsimp only [canonicalProjectiveFieldBaseChangeChartIso, Iso.trans_hom,
    finiteProjectiveStandardChartToBase]
  simp only [Category.assoc, IsPullback.isoPullback_hom_fst,
    Scheme.isoOfEq_hom_ι_assoc]

def canonicalProjectiveFieldBaseChangeChartTensorIso {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    finiteProjectiveStandardChart (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j ≅
      Spec (.of (K ⊗[k] Γ(finiteProjectiveStandardChart i j, ⊤))) := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  exact canonicalProjectiveFieldBaseChangeChartIso (K := K) i j ≪≫
    finiteSchemeActualFieldBaseChangeIso (K := K) (finiteProjectiveStandardChartToBase i j)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem canonicalProjectiveFieldBaseChangeChartTensorIso_toOriginal {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartToBase_isFinite i j
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    letI : IsAffine (finiteProjectiveStandardChart i j) :=
      isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
    (canonicalProjectiveFieldBaseChangeChartTensorIso (K := K) i j).hom ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : Γ(finiteProjectiveStandardChart i j, ⊤) →ₐ[k]
          K ⊗[k] Γ(finiteProjectiveStandardChart i j, ⊤)).toRingHom) ≫
      (finiteProjectiveStandardChart i j).isoSpec.inv ≫
      (finiteProjectiveStandardChartOpen i j).ι =
    (finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j).ι ≫
      pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ ambientToBase) := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  letI : IsAffine (finiteProjectiveStandardChart i j) :=
    isAffine_of_isAffineHom (finiteProjectiveStandardChartToBase i j)
  unfold canonicalProjectiveFieldBaseChangeChartTensorIso
  simp only [Iso.trans_hom, Category.assoc]
  have h := finiteSchemeActualFieldBaseChangeIso_hom_toOriginal (K := K)
    (finiteProjectiveStandardChartToBase i j)
  calc
    _ = (canonicalProjectiveFieldBaseChangeChartIso (K := K) i j).hom ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K)))
          (finiteProjectiveStandardChartToBase i j) ≫
        (finiteProjectiveStandardChartOpen i j).ι := by
      simpa only [Category.assoc] using
        congrArg (fun a => (canonicalProjectiveFieldBaseChangeChartIso (K := K) i j).hom ≫
          a ≫ (finiteProjectiveStandardChartOpen i j).ι) h
    _ = _ := canonicalProjectiveFieldBaseChangeChartIso_toOriginal (K := K) i j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem canonicalProjectiveFieldBaseChangeChartTensorIso_toField {Z : Scheme.{u}}
    (i : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 4) k))
    [IsFinite (i ≫ ambientToBase)] (j : Fin 4) :
    letI := finiteProjectiveStandardChartCoefficientAlgebra i j
    (canonicalProjectiveFieldBaseChangeChartTensorIso (K := K) i j).hom ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap K (K ⊗[k] Γ(finiteProjectiveStandardChart i j, ⊤)))) =
    (finiteProjectiveStandardChartOpen
      (canonicalProjectiveFieldBaseChangeEmbedding (K := K) i) j).ι ≫
      pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        (i ≫ ambientToBase) := by
  letI := finiteProjectiveStandardChartToBase_isFinite i j
  letI := finiteProjectiveStandardChartCoefficientAlgebra i j
  unfold canonicalProjectiveFieldBaseChangeChartTensorIso
  simp only [Iso.trans_hom, Category.assoc,
    finiteSchemeActualFieldBaseChangeIso_hom_toField,
    canonicalProjectiveFieldBaseChangeChartIso_toField] <;> rfl

end PfaffianDescent
