import PfaffianDescent.GrassmannianFrameProjectivePullback
import PfaffianDescent.RelativeProjectiveLinearSystem
import PfaffianDescent.GrassmannianProper

/-!
# Properness of the projective Grassmannian-frame family

The glued projective-frame family restricts over every standard
Grassmannian chart to the usual relative projective space.  Hence its global
projection is proper, and so is its composite structure morphism over a
Noetherian coefficient ring.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable (K : Type u) [CommRing K] {m n : ℕ}
variable {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A projective-frame overlap is the inverse image of the corresponding
Grassmannian overlap inside a local chart. -/
theorem grassmannianFrameProjectiveAtlasι_range
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    Set.range (grassmannianFrameProjectiveAtlasι K i j) =
      (toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m)
          (GrassmannianChartRing K m n)))) ⁻¹'
        Set.range (grassmannianAtlasι K i j) := by
  exact CategoryTheory.Limits.Types.range_fst_of_isPullback
    ((isPullback_projectiveCoefficientMap
      (algebraMap (GrassmannianChartRing K m n)
        (GrassmannianOverlapRing K (grassmannianChartChange i j))) _ _
      (by simp)).map Scheme.forget)

/-- A Grassmannian overlap is the inverse image of the second global chart
inside the first global chart. -/
theorem grassmannianAtlasι_range
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    Set.range (grassmannianAtlasι K i j) =
      (grassmannianChartι K i) ⁻¹' Set.range (grassmannianChartι K j) := by
  have h : IsPullback (grassmannianAtlasι K i j)
      (grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i)
      (grassmannianChartι K i) (grassmannianChartι K j) :=
    IsPullback.of_isLimit (grassmannianChart_intersection K i j)
  exact CategoryTheory.Limits.Types.range_fst_of_isPullback
    (h.map Scheme.forget)

/-- The inverse image of a standard Grassmannian chart under the global
projective-frame projection is exactly the corresponding glued projective
chart. -/
theorem grassmannianFrameProjectiveToGrassmannian_preimage_chart
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveToGrassmannian K d e ⁻¹ᵁ
        (grassmannianChartι K i).opensRange =
      (grassmannianFrameProjectiveChartι K d e i).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  constructor
  · intro hx
    change grassmannianFrameProjectiveToGrassmannian K d e x ∈
      (grassmannianChartι K i).opensRange at hx
    rw [Scheme.Hom.mem_opensRange] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨j, y, hy⟩ :=
      grassmannianFrameProjectiveChartι_jointly_surjective K d e x
    have hchart := grassmannianFrameProjectiveChartι_toGrassmannian K d e j
    have hbaseEq : grassmannianChartι K i z =
        grassmannianChartι K j
          (toBase (⊥ : HomogeneousIdeal
            (MvPolynomial.homogeneousSubmodule (Fin m)
              (GrassmannianChartRing K m n))) y) := by
      rw [hz, ← hy]
      have h := congrArg (fun q => q y) hchart
      simp only [Scheme.Hom.comp_apply] at h
      convert h using 1
      rfl
    have hbaseMem : toBase (⊥ : HomogeneousIdeal
          (MvPolynomial.homogeneousSubmodule (Fin m)
            (GrassmannianChartRing K m n))) y ∈
        Set.range (grassmannianAtlasι K j i) := by
      rw [grassmannianAtlasι_range K j i]
      exact ⟨z, hbaseEq⟩
    have hyMem : y ∈ Set.range
        (grassmannianFrameProjectiveAtlasι K j i) := by
      rw [grassmannianFrameProjectiveAtlasι_range K j i]
      exact hbaseMem
    obtain ⟨w, hw⟩ := hyMem
    change ∃ y, grassmannianFrameProjectiveChartι K d e i y = x
    refine ⟨(grassmannianFrameProjectiveAtlasTransition K d e j i ≫
      grassmannianFrameProjectiveAtlasι K i j) w, ?_⟩
    have hglue := congrArg (fun q => q w)
      (grassmannianFrameProjectiveChartι_glue K d e j i)
    simp only [Scheme.Hom.comp_apply] at hglue
    calc
      ((grassmannianFrameProjectiveAtlasTransition K d e j i ≫
          grassmannianFrameProjectiveAtlasι K i j) ≫
          grassmannianFrameProjectiveChartι K d e i) w =
        (grassmannianFrameProjectiveAtlasι K j i ≫
          grassmannianFrameProjectiveChartι K d e j) w := by
            simpa only [Scheme.Hom.comp_apply] using hglue
      _ = x := by simp only [Scheme.Hom.comp_apply, hw, hy]
  · intro hx
    change (∃ y, grassmannianFrameProjectiveChartι K d e i y = x) at hx
    obtain ⟨y, hy⟩ := hx
    change grassmannianFrameProjectiveToGrassmannian K d e x ∈
      (grassmannianChartι K i).opensRange
    change ∃ z, grassmannianChartι K i z =
      grassmannianFrameProjectiveToGrassmannian K d e x
    refine ⟨toBase (⊥ : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule (Fin m)
        (GrassmannianChartRing K m n))) y, ?_⟩
    rw [← hy, ← Scheme.Hom.comp_apply,
      grassmannianFrameProjectiveChartι_toGrassmannian,
      Scheme.Hom.comp_apply]
    rfl

/-- Each local projective-frame chart is the Cartesian restriction of the
global family to the corresponding standard Grassmannian chart. -/
theorem isPullback_grassmannianFrameProjective_chart
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsPullback
      (toBase (⊥ : HomogeneousIdeal
        (MvPolynomial.homogeneousSubmodule (Fin m)
          (GrassmannianChartRing K m n))))
      (grassmannianFrameProjectiveChartι K d e i)
      (grassmannianChartι K i)
      (grassmannianFrameProjectiveToGrassmannian K d e) := by
  apply IsOpenImmersion.isPullback
  · exact grassmannianFrameProjectiveChartι_toGrassmannian K d e i
  · exact grassmannianFrameProjectiveToGrassmannian_preimage_chart K d e i

section Noetherian

variable [IsNoetherianRing K]

/-- The glued projective-frame family is proper over the Grassmannian. -/
instance grassmannianFrameProjectiveToGrassmannian_isProper
    (e : Fin (m + n) ≃ Monomials τ d) :
    IsProper (grassmannianFrameProjectiveToGrassmannian K d e) := by
  let 𝒰 := (grassmannianGlueData K m n).openCover
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsProper) 𝒰]
  change ∀ i : ULift.{u} (Equiv.Perm (Fin m ⊕ Fin n)), IsProper _
  intro i
  change IsProper (pullback.snd
    (grassmannianFrameProjectiveToGrassmannian K d e)
    (grassmannianChartι K i.down))
  let h := (isPullback_grassmannianFrameProjective_chart K d e i.down).flip
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper
    h.isoPullback.hom (pullback.snd
      (grassmannianFrameProjectiveToGrassmannian K d e)
      (grassmannianChartι K i.down))]
  rw [h.isoPullback_hom_snd]
  exact isProper_toBase _

/-- Structure morphism of the projective-frame family over the coefficient
ring. -/
noncomputable def grassmannianFrameProjectiveToBase
    (e : Fin (m + n) ≃ Monomials τ d) :
    grassmannianFrameProjectiveScheme K d e ⟶ Spec (.of K) :=
  grassmannianFrameProjectiveToGrassmannian K d e ≫
    grassmannianToBase K m n

/-- The global equation represented by the projective-frame family is over
the original coefficient ring. -/
theorem grassmannianFrameProjectiveToGlobalParameters_toBase
    (e : Fin (m + n) ≃ Monomials τ d) :
    grassmannianFrameProjectiveToGlobalParameters K d e ≫
        projectiveParametersToBase K τ d =
      grassmannianFrameProjectiveToBase K d e := by
  apply Multicoequalizer.hom_ext
    (grassmannianFrameProjectiveGlueData K d e).toGlueData.diagram
  intro i
  change grassmannianFrameProjectiveChartι K d e i.down ≫
      (grassmannianFrameProjectiveToGlobalParameters K d e ≫
        projectiveParametersToBase K τ d) =
    grassmannianFrameProjectiveChartι K d e i.down ≫
      (grassmannianFrameProjectiveToGrassmannian K d e ≫
        grassmannianToBase K m n)
  rw [← Category.assoc,
    grassmannianFrameProjectiveChartι_toGlobalParameters,
    grassmannianFrameProjectiveChartToGlobalParameters,
    grassmannianChartHomogeneousFrameToGlobalParameters_toBase]
  rw [← Category.assoc,
    grassmannianFrameProjectiveChartι_toGrassmannian,
    Category.assoc, grassmannianChartι_toBase]
  rfl

/-- The total projective-frame family is proper over the coefficient ring. -/
instance grassmannianFrameProjectiveToBase_isProper
    (e : Fin (m + n) ≃ Monomials τ d) :
    IsProper (grassmannianFrameProjectiveToBase K d e) := by
  unfold grassmannianFrameProjectiveToBase
  infer_instance

/-! ## Proper family over the closure of a spread -/

/-- The projective equation family over the scheme-theoretic image of a
Grassmannian-valued family. -/
noncomputable def grassmannianFrameProjectiveImageFamily
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) : Scheme.{u} :=
  grassmannianFrameProjectiveFamilyPullback K d e f.imageι

/-- Projection of the image-closure projective family to the
scheme-theoretic image of the classifying map. -/
noncomputable def grassmannianFrameProjectiveImageFamilyToImage
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveImageFamily K d e f ⟶ f.image :=
  grassmannianFrameProjectiveFamilyPullbackToBase K d e f.imageι

/-- Structure morphism of the image-closure projective family over the
coefficient ring. -/
noncomputable def grassmannianFrameProjectiveImageFamilyToBase
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveImageFamily K d e f ⟶ Spec (.of K) :=
  grassmannianFrameProjectiveImageFamilyToImage K d e f ≫
    f.imageι ≫ grassmannianToBase K m n

/-- The equation represented by a point of the image-closure projective
family. -/
noncomputable def grassmannianFrameProjectiveImageFamilyToGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveImageFamily K d e f ⟶
      projectiveParameters K τ d :=
  grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e f.imageι

/-- The image-closure projective family is proper over the coefficient
ring. -/
instance grassmannianFrameProjectiveImageFamilyToBase_isProper
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    IsProper (grassmannianFrameProjectiveImageFamilyToBase K d e f) := by
  unfold grassmannianFrameProjectiveImageFamilyToBase
    grassmannianFrameProjectiveImageFamilyToImage
    grassmannianFrameProjectiveFamilyPullbackToBase
    grassmannianFrameProjectiveImageFamily
    grassmannianFrameProjectiveFamilyPullback
  haveI : IsProper (f.imageι ≫ grassmannianToBase K m n) := by
    infer_instance
  change IsProper
    (pullback.snd (grassmannianFrameProjectiveToGrassmannian K d e) f.imageι ≫
      (f.imageι ≫ grassmannianToBase K m n))
  infer_instance

/-- The equation morphism of the image-closure family lies over the original
coefficient ring. -/
theorem grassmannianFrameProjectiveImageFamilyToGlobalParameters_toBase
    (e : Fin (m + n) ≃ Monomials τ d) {X : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) :
    grassmannianFrameProjectiveImageFamilyToGlobalParameters K d e f ≫
        projectiveParametersToBase K τ d =
      grassmannianFrameProjectiveImageFamilyToBase K d e f := by
  unfold grassmannianFrameProjectiveImageFamilyToGlobalParameters
    grassmannianFrameProjectiveImageFamilyToBase
    grassmannianFrameProjectiveImageFamilyToImage
    grassmannianFrameProjectiveImageFamily
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
    grassmannianFrameProjectiveFamilyPullbackToBase
    grassmannianFrameProjectiveFamilyPullback
  rw [Category.assoc,
    grassmannianFrameProjectiveToGlobalParameters_toBase]
  unfold grassmannianFrameProjectiveToBase
  rw [← Category.assoc, pullback.condition]
  simp only [Category.assoc]

/-- The fibre of the proper image-closure family, with its classifying map
left in the literal factorized form through the scheme-theoretic image. -/
noncomputable def grassmannianFrameProjectiveImageFamily_rawBaseChangeIso
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    pullback (grassmannianFrameProjectiveImageFamilyToImage K d e f)
        (g ≫ f.toImage) ≅
      grassmannianFrameProjectiveFamilyPullback K d e
        ((g ≫ f.toImage) ≫ f.imageι) :=
  grassmannianFrameProjectiveFamilyPullback_baseChangeIso
    K d e f.imageι (g ≫ f.toImage)

/-- The fibre of the proper image-closure family along a map to the original
spread base is canonically the projective family classified by the composite
Grassmannian map. -/
noncomputable def grassmannianFrameProjectiveImageFamily_baseChangeIso
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    pullback (grassmannianFrameProjectiveImageFamilyToImage K d e f)
        (g ≫ f.toImage) ≅
      grassmannianFrameProjectiveFamilyPullback K d e (g ≫ f) := by
  unfold grassmannianFrameProjectiveImageFamilyToImage
  simpa only [Category.assoc, f.toImage_imageι] using
    (grassmannianFrameProjectiveFamilyPullback_baseChangeIso
      K d e f.imageι (g ≫ f.toImage))

set_option backward.isDefEq.respectTransparency false in
/-- The inverse image-family base-change isomorphism preserves the point of
the base scheme. -/
theorem grassmannianFrameProjectiveImageFamily_baseChangeIso_inv_toBase
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    (grassmannianFrameProjectiveImageFamily_rawBaseChangeIso K d e f g).inv ≫
        pullback.snd (grassmannianFrameProjectiveImageFamilyToImage K d e f)
          (g ≫ f.toImage) =
      grassmannianFrameProjectiveFamilyPullbackToBase K d e
        ((g ≫ f.toImage) ≫ f.imageι) := by
  unfold grassmannianFrameProjectiveImageFamily_rawBaseChangeIso
    grassmannianFrameProjectiveImageFamilyToImage
    grassmannianFrameProjectiveFamilyPullback_baseChangeIso
    grassmannianFrameProjectiveFamilyPullbackToBase
    grassmannianFrameProjectiveImageFamily
  simpa only using
    (pullbackLeftPullbackSndIso_inv_snd_snd
      (grassmannianFrameProjectiveToGrassmannian K d e) f.imageι
      (g ≫ f.toImage))

set_option backward.isDefEq.respectTransparency false in
/-- Transport through the inverse image-family base-change isomorphism does
not change the represented ambient homogeneous equation. -/
theorem grassmannianFrameProjectiveImageFamily_baseChangeIso_inv_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X) :
    (grassmannianFrameProjectiveImageFamily_rawBaseChangeIso K d e f g).inv ≫
        pullback.fst (grassmannianFrameProjectiveImageFamilyToImage K d e f)
          (g ≫ f.toImage) ≫
        grassmannianFrameProjectiveImageFamilyToGlobalParameters K d e f =
      grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
        ((g ≫ f.toImage) ≫ f.imageι) := by
  unfold grassmannianFrameProjectiveImageFamily_rawBaseChangeIso
    grassmannianFrameProjectiveImageFamilyToImage
    grassmannianFrameProjectiveImageFamilyToGlobalParameters
    grassmannianFrameProjectiveFamilyPullback_baseChangeIso
    grassmannianFrameProjectiveFamilyPullbackToGlobalParameters
    grassmannianFrameProjectiveFamilyPullbackToBase
    grassmannianFrameProjectiveImageFamily
  simpa only using
    (pullbackLeftPullbackSndIso_inv_fst_assoc
      (grassmannianFrameProjectiveToGrassmannian K d e) f.imageι
      (g ≫ f.toImage)
      (grassmannianFrameProjectiveToGlobalParameters K d e))

/-- Transport a point of the literal generic fibre into the proper family
over the scheme-theoretic image. -/
noncomputable def grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e
      ((g ≫ f.toImage) ≫ f.imageι)) :
    Y ⟶ grassmannianFrameProjectiveImageFamily K d e f :=
  s ≫ (grassmannianFrameProjectiveImageFamily_rawBaseChangeIso K d e f g).inv ≫
    pullback.fst (grassmannianFrameProjectiveImageFamilyToImage K d e f)
      (g ≫ f.toImage)

set_option backward.isDefEq.respectTransparency false in
/-- The transported fibre point lies over the prescribed point of the
scheme-theoretic image. -/
theorem grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toImage
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e
      ((g ≫ f.toImage) ≫ f.imageι))
    (hs : s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
      ((g ≫ f.toImage) ≫ f.imageι) = 𝟙 Y) :
    grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint K d e f g s ≫
        grassmannianFrameProjectiveImageFamilyToImage K d e f =
      g ≫ f.toImage := by
  unfold grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint
  let E := grassmannianFrameProjectiveImageFamily_rawBaseChangeIso K d e f g
  let pi := grassmannianFrameProjectiveImageFamilyToImage K d e f
  have hcondition :
      pullback.fst pi (g ≫ f.toImage) ≫ pi =
        pullback.snd pi (g ≫ f.toImage) ≫ (g ≫ f.toImage) :=
    pullback.condition
  have hbase :=
    grassmannianFrameProjectiveImageFamily_baseChangeIso_inv_toBase
      K d e f g
  calc
    (s ≫ E.inv ≫ pullback.fst pi (g ≫ f.toImage)) ≫ pi =
        s ≫ E.inv ≫ (pullback.fst pi (g ≫ f.toImage) ≫ pi) := by
          simp only [Category.assoc]
    _ = s ≫ E.inv ≫
        (pullback.snd pi (g ≫ f.toImage) ≫ (g ≫ f.toImage)) := by
          exact congrArg (fun h => s ≫ E.inv ≫ h) hcondition
    _ = (s ≫ (E.inv ≫ pullback.snd pi (g ≫ f.toImage))) ≫
        (g ≫ f.toImage) := by simp only [Category.assoc]
    _ = (s ≫ grassmannianFrameProjectiveFamilyPullbackToBase K d e
        ((g ≫ f.toImage) ≫ f.imageι)) ≫ (g ≫ f.toImage) := by
          exact congrArg (fun h => (s ≫ h) ≫ (g ≫ f.toImage)) hbase
    _ = g ≫ f.toImage := by rw [hs, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Transporting a literal fibre point into the proper image family
preserves its represented ambient homogeneous equation. -/
theorem grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) {X Y : Scheme.{u}}
    (f : X ⟶ grassmannianScheme K m n) (g : Y ⟶ X)
    (s : Y ⟶ grassmannianFrameProjectiveFamilyPullback K d e
      ((g ≫ f.toImage) ≫ f.imageι)) :
    grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint K d e f g s ≫
        grassmannianFrameProjectiveImageFamilyToGlobalParameters K d e f =
      s ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
        ((g ≫ f.toImage) ≫ f.imageι) := by
  unfold grassmannianFrameProjectiveImageFamilyPointOfRawFiberPoint
  let E := grassmannianFrameProjectiveImageFamily_rawBaseChangeIso K d e f g
  let pi := grassmannianFrameProjectiveImageFamilyToImage K d e f
  let P := grassmannianFrameProjectiveImageFamilyToGlobalParameters K d e f
  have hglobal :=
    grassmannianFrameProjectiveImageFamily_baseChangeIso_inv_toGlobalParameters
      K d e f g
  calc
    (s ≫ E.inv ≫ pullback.fst pi (g ≫ f.toImage)) ≫ P =
        s ≫ (E.inv ≫ pullback.fst pi (g ≫ f.toImage) ≫ P) := by
          simp only [Category.assoc]
    _ = s ≫ grassmannianFrameProjectiveFamilyPullbackToGlobalParameters K d e
        ((g ≫ f.toImage) ≫ f.imageι) := congrArg (fun h => s ≫ h) hglobal

end Noetherian

end PfaffianDescent
