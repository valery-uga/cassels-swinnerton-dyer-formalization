import PfaffianDescent.VoisinProjectiveCubicCohomology
import PfaffianDescent.VoisinSheafStalk
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# The standard affine cover of projective three-space

This file sets up the four-coordinate cover used to calculate the ambient
line-bundle cohomology in Voisin's argument.  It constructs the raw Cech
complex of the concrete negative twists, proves that the cover is exhaustive,
and proves that every finite intersection in its Cech nerve is affine.

It also promotes stalkwise invertibility of multiplication by a homogeneous
element to an isomorphism after restriction to the corresponding basic open.
This is the local-triviality input for identifying the Cech terms with
homogeneous Laurent fractions.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open MvPolynomial
open scoped DirectSum
open DirectSum SetLike

universe u w v₁ v₂ u₁ u₂

namespace ProjectiveNegativeTwist

/-- Restriction to an open is an isomorphism if the original map is an
isomorphism at every stalk belonging to that open. -/
theorem restrict_map_isIso_of_stalk
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ x : U, IsIso ((schemeModuleStalkFunctor X (U.ι x)).map f)) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  let g := (Scheme.Modules.restrictFunctor U.ι).map f
  have hgSheaf : IsIso
      ((SheafOfModules.toSheaf (U : Scheme).ringCatSheaf).map g) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    let L := Scheme.Modules.restrictFunctor U.ι ⋙
      Scheme.Modules.toPresheaf (U : Scheme) ⋙
      TopCat.Presheaf.stalkFunctor _ x
    let R := Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor _ (U.ι x)
    let e := Scheme.Modules.restrictStalkNatIso U.ι x
    let a := L.map f
    let d := R.map f
    change IsIso a
    haveI : IsIso d := by
      change IsIso ((schemeModuleStalkFunctor X (U.ι x)).map f)
      exact h x
    have hnat : a ≫ (e.app N).hom = (e.app M).hom ≫ d :=
      e.hom.naturality f
    have ha : a = (e.app M).hom ≫ d ≫ (e.app N).inv := by
      rw [← cancel_mono (e.app N).hom]
      rw [hnat]
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ha]
    infer_instance
  let q := (SheafOfModules.toSheaf (U : Scheme).ringCatSheaf).map g
  have hqForget : IsIso ((TopCat.Sheaf.forget _ (U : Scheme)).map q) :=
    @Functor.map_isIso _ _ _ _ _ _
      (TopCat.Sheaf.forget _ (U : Scheme)) q hgSheaf
  have hgPresheaf : IsIso
      ((Scheme.Modules.toPresheaf (U : Scheme)).map g) := by
    change IsIso ((TopCat.Sheaf.forget _ (U : Scheme)).map q)
    exact hqForget
  letI : IsIso ((Scheme.Modules.toPresheaf (U : Scheme)).map g) := hgPresheaf
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf (U : Scheme))

/-- Sections of a restricted module over the top open are canonically the
sections of the original module over the open being restricted to. -/
def moduleRestrictTopIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Γ(M.restrict U.ι, ⊤) ≅ Γ(M, U) :=
  M.restrictAppIso U.ι ⊤ ≪≫
    M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

private lemma natTrans_app_transport
    {C : Type u₁} {D : Type u₂} [Category.{v₁, u₁} C] [Category.{v₂, u₂} D]
    {F G : C ⥤ D} (τ : F ⟶ G) {A B : C} (e : A ≅ B) :
    τ.app A = F.map e.hom ≫ τ.app B ≫ G.map e.inv := by
  rw [← cancel_mono (G.map e.hom)]
  simp only [Category.assoc]
  rw [← τ.naturality e.hom]
  simp

private lemma functorToFunctor_map_comp_app
    {C : Type u₁} {D : Type u₂} {E : Type*}
    [Category.{v₁, u₁} C] [Category.{v₂, u₂} D] [Category E]
    (F : C ⥤ D ⥤ E) {A B C' : C} (f : A ⟶ B) (g : B ⟶ C') (X : D) :
    (F.map (f ≫ g)).app X = (F.map f).app X ≫ (F.map g).app X := by
  exact congrArg (fun q => q.app X) (F.map_comp f g)

/-- The top-section identification for restriction is natural in the module. -/
lemma moduleRestrictTopIso_naturality
    {X : Scheme.{u}} {M N : X.Modules} (t : M ⟶ N) (U : X.Opens) :
    ((Scheme.Modules.toPresheaf X).map t).app (op U) =
      (moduleRestrictTopIso M U).inv ≫
        ((Scheme.Modules.toPresheaf (U : Scheme)).map
          ((Scheme.Modules.restrictFunctor U.ι).map t)).app (op ⊤) ≫
        (moduleRestrictTopIso N U).hom := by
  have hM : (moduleRestrictTopIso M U).inv =
      M.presheaf.map (eqToHom U.ι_image_top).op := rfl
  have hN : (moduleRestrictTopIso N U).hom =
      N.presheaf.map (eqToHom U.ι_image_top.symm).op := rfl
  have ha : ((Scheme.Modules.toPresheaf (U : Scheme)).map
      ((Scheme.Modules.restrictFunctor U.ι).map t)).app (op ⊤) =
      ((Scheme.Modules.toPresheaf X).map t).app (op (U.ι ''ᵁ ⊤)) := rfl
  rw [hM, hN, ha]
  exact natTrans_app_transport ((Scheme.Modules.toPresheaf X).map t)
    (eqToIso U.ι_image_top).op

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A projective basic open with its ambient scheme retained in the type. -/
def homogeneousBasicOpen (s : A) : Scheme.Opens (Proj 𝒜) :=
  ProjectiveSpectrum.basicOpen 𝒜 s

/-- Multiplication by a homogeneous element becomes an isomorphism after
restriction to its projective basic open. -/
theorem restrict_mulHomogeneous_isIso_on_basicOpen {d : ℕ}
    (s : 𝒜 d) (m : ℕ)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    IsIso ((Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).map
        (mulHomogeneous 𝒜 s m)) := by
  let U := homogeneousBasicOpen 𝒜 (s : A)
  apply restrict_map_isIso_of_stalk U
  intro x
  letI : (pointIdeal 𝒜 (U.ι x)).IsPrime :=
    ProjectiveSpectrum.isPrime (U.ι x)
  have hsx : (s : A) ∈ (pointIdeal 𝒜 (U.ι x)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (s : A) (U.ι x)).mp x.property
  change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
    (mulHomogeneousPresheaf 𝒜 s m))
  exact mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    𝒜 s m (U.ι x) hsx hspan

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "S" => MvPolynomial (Fin 4) K
local notation "𝒮" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- A standard homogeneous coordinate, regarded as a degree-one element. -/
def p3Coordinate (i : Fin 4) : 𝒮 1 :=
  ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩

/-- The four standard affine opens of projective three-space. -/
def p3StandardOpen (i : Fin 4) : Scheme.Opens (Proj 𝒮) :=
  ProjectiveSpectrum.basicOpen 𝒮 (p3Coordinate K i : S)

/-- The four coordinates generate the irrelevant ideal of the homogeneous
coordinate ring of projective three-space. -/
lemma p3Coordinates_span_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒮).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 4 => (p3Coordinate K i : S)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hpvars : p ∈ MvPolynomial.idealOfVars (Fin 4) K := by
    rw [← pow_one (MvPolynomial.idealOfVars (Fin 4) K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro mon hmon
    have he : mon.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hmon).symm
    exact he ▸ hn
  change p ∈ Ideal.span (Set.range fun i : Fin 4 => MvPolynomial.X i)
  simpa only [MvPolynomial.idealOfVars] using hpvars

/-- The four standard coordinate opens cover projective three-space. -/
lemma p3StandardOpen_iSup :
    ⨆ i : Fin 4, p3StandardOpen (K := K) i = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  exact p3Coordinates_span_irrelevant K

/-- On a standard coordinate chart, multiplication by the appropriate power
of that coordinate identifies the negative twist with the zero twist. -/
theorem restrict_mulCoordinatePower_isIso
    (i : Fin 4) (m : ℕ) (hm : 0 < m) :
    IsIso ((Scheme.Modules.restrictFunctor
      (p3StandardOpen (K := K) i).ι).map
        (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0)) := by
  have hU : homogeneousBasicOpen PS
      (degreeOnePower PS (p3Coordinate K i) m : S) =
      p3StandardOpen (K := K) i := by
    change ProjectiveSpectrum.basicOpen PS
        ((MvPolynomial.X i) ^ m) =
      ProjectiveSpectrum.basicOpen PS (MvPolynomial.X i)
    exact ProjectiveSpectrum.basicOpen_pow PS (MvPolynomial.X i) m hm
  rw [← hU]
  apply restrict_mulHomogeneous_isIso_on_basicOpen
  exact (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
    rintro _ ⟨i, rfl⟩
    exact ⟨p3Coordinate K i, rfl⟩))

/-- The concrete negative twist is locally free of rank one on every
standard coordinate chart. -/
def p3NegativeTwistStandardOpenIsoUnit
    (i : Fin 4) (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.restrictFunctor
      (p3StandardOpen (K := K) i).ι).obj (sheafOfModules PS m) ≅
      SheafOfModules.unit
        (p3StandardOpen (K := K) i : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor
    (p3StandardOpen (K := K) i).ι
  let s := degreeOnePower PS (p3Coordinate K i) m
  let f : sheafOfModules PS m ⟶ sheafOfModules PS 0 := by
    simpa using mulHomogeneous PS s 0
  letI : IsIso (R.map f) := by
    dsimp only [f, s]
    simpa using restrict_mulCoordinatePower_isIso K i m hm
  exact asIso (R.map f) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso
      (p3StandardOpen (K := K) i).ι

/-- Multiplication by `X_i^m` is invertible after restricting to any open
contained in the standard chart `D_+(X_i)`.  This form applies directly to
every nonempty intersection in the standard Cech nerve. -/
theorem restrict_mulCoordinatePower_isIso_of_le
    (U : Scheme.Opens (Proj PS)) (i : Fin 4) (m : ℕ)
    (hU : U ≤ p3StandardOpen (K := K) i) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (mulHomogeneous PS (degreeOnePower PS (p3Coordinate K i) m) 0)) := by
  apply restrict_map_isIso_of_stalk U
  intro x
  letI : (pointIdeal PS (U.ι x)).IsPrime :=
    ProjectiveSpectrum.isPrime (U.ι x)
  have hXi : (MvPolynomial.X i : S) ∈
      (pointIdeal PS (U.ι x)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen PS
      (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
  have hsx : (degreeOnePower PS (p3Coordinate K i) m : S) ∈
      (pointIdeal PS (U.ι x)).primeCompl := by
    change (MvPolynomial.X i : S) ^ m ∈
      (pointIdeal PS (U.ι x)).primeCompl
    exact Submonoid.pow_mem _ hXi m
  change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
    (mulHomogeneousPresheaf PS
      (degreeOnePower PS (p3Coordinate K i) m) 0))
  apply mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    PS (degreeOnePower PS (p3Coordinate K i) m) 0 (U.ι x) hsx
  exact (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
    rintro _ ⟨j, rfl⟩
    exact ⟨p3Coordinate K j, rfl⟩))

/-- The negative twist is trivial on any open lying inside one standard
coordinate chart. -/
def p3NegativeTwistOpenIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (sheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K i) m
  let f : sheafOfModules PS m ⟶ sheafOfModules PS 0 := by
    simpa using mulHomogeneous PS s 0
  letI : IsIso (R.map f) := by
    dsimp only [f, s]
    simpa using restrict_mulCoordinatePower_isIso_of_le K U i m hU
  exact asIso (R.map f) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- Sections of the negative twist on an open contained in `D_+(X_i)` are
canonically identified, using multiplication by `X_i^m`, with structure
sheaf sections on that open. -/
def p3NegativeTwistSectionsIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    Γ(sheafOfModules PS m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := p3NegativeTwistOpenIsoUnit K U i hU m
  exact (moduleRestrictTopIso (sheafOfModules PS m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

/-- On a homogeneous basic open contained in `D_+(X_i)`, sections of the
negative twist are identified with the degree-zero homogeneous localization.
The identification sends a section to its product with `X_i^m`. -/
def p3NegativeTwistBasicOpenIsoAway
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    Γ(sheafOfModules PS m, AlgebraicGeometry.Proj.basicOpen PS f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS f) := by
  let U := AlgebraicGeometry.Proj.basicOpen PS f
  have hU : U ≤ p3StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (MvPolynomial.X i) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact p3NegativeTwistSectionsIsoUnit K U i hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).symm

/-- Naturality of the standard identification of projective basic-open
functions with degree-zero homogeneous localizations. -/
theorem basicOpenIsoAway_inv_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) :
    (AlgebraicGeometry.Proj PS).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv =
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv ≫
      CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx) := by
  rw [← cancel_mono (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom]
  rw [AlgebraicGeometry.Proj.awayMap_awayToSection]
  rw [← AlgebraicGeometry.Proj.basicOpenIsoAway_hom PS f hf hd]
  simp

/-- Multiplication by `X_i^m`, followed by the zero-twist/unit
identification, as one global sheaf morphism. -/
def negativeTwistTrivializationHom (i : Fin 4) (m : ℕ) :
    sheafOfModules PS m ⟶
      SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf := by
  let s := degreeOnePower PS (p3Coordinate K i) m
  let f : sheafOfModules PS m ⟶ sheafOfModules PS 0 := by
    simpa using mulHomogeneous PS s 0
  exact f ≫ (unitIsoZeroTwist PS).inv

lemma p3NegativeTwistOpenIsoUnit_hom
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (p3NegativeTwistOpenIsoUnit K U i hU m).hom =
      (Scheme.Modules.restrictFunctor U.ι).map
          (negativeTwistTrivializationHom K i m) ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom := by
  dsimp [p3NegativeTwistOpenIsoUnit, negativeTwistTrivializationHom]
  rfl

lemma p3NegativeTwistOpenIsoUnit_app_top
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
      (p3NegativeTwistOpenIsoUnit K U i hU m)).app (op ⊤)).hom =
      ((Scheme.Modules.toPresheaf (U : Scheme)).map
        ((Scheme.Modules.restrictFunctor U.ι).map
          (negativeTwistTrivializationHom K i m))).app (op ⊤) ≫
      ((Scheme.Modules.toPresheaf (U : Scheme)).map
        (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤) := by
  change ((Scheme.Modules.toPresheaf (U : Scheme)).map
      (p3NegativeTwistOpenIsoUnit K U i hU m).hom).app (op ⊤) = _
  rw [p3NegativeTwistOpenIsoUnit_hom]
  exact functorToFunctor_map_comp_app
    (Scheme.Modules.toPresheaf (U : Scheme)) _ _ (op ⊤)

lemma restrictUnit_app_top_topIso
    (U : Scheme.Opens (Proj PS)) :
    ((Scheme.Modules.toPresheaf (U : Scheme)).map
        (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤) ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom =
      (moduleRestrictTopIso
        (SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf) U).hom := by
  ext r
  simp only [Functor.comp_obj, Scheme.Modules.toPresheaf_obj,
    Scheme.Modules.restrictUnitIso, Functor.op_obj, Scheme.Opens.ι_appIso,
    Scheme.Opens.topIso_hom, eqToHom_op, moduleRestrictTopIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The hom of the chart-section isomorphism is the component of the single
global multiplication morphism. -/
theorem p3NegativeTwistSectionsIsoUnit_hom_topIso
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (p3NegativeTwistSectionsIsoUnit K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (negativeTwistTrivializationHom K i m)).app (op U) := by
  rw [moduleRestrictTopIso_naturality
    (negativeTwistTrivializationHom K i m) U]
  let eM := (moduleRestrictTopIso (sheafOfModules PS m) U).inv
  let b := (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
    (p3NegativeTwistOpenIsoUnit K U i hU m)).app (op ⊤)).hom
  let a := ((Scheme.Modules.toPresheaf (U : Scheme)).map
    ((Scheme.Modules.restrictFunctor U.ι).map
      (negativeTwistTrivializationHom K i m))).app (op ⊤)
  let r := ((Scheme.Modules.toPresheaf (U : Scheme)).map
    (Scheme.Modules.restrictUnitIso U.ι).hom).app (op ⊤)
  let q := (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    U.topIso.hom
  let eN := (moduleRestrictTopIso
    (SheafOfModules.unit (AlgebraicGeometry.Proj PS).ringCatSheaf) U).hom
  have hdef : (p3NegativeTwistSectionsIsoUnit K U i hU m).hom = eM ≫ b := rfl
  have hb : b = a ≫ r := p3NegativeTwistOpenIsoUnit_app_top K U i hU m
  have hr : r ≫ q = eN := restrictUnit_app_top_topIso K U
  rw [hdef, hb]
  change (eM ≫ a ≫ r) ≫ q = eM ≫ a ≫ eN
  simp only [Category.assoc]
  rw [hr]

/-- The chart trivialization, with values transported back to ambient
structure-sheaf sections. -/
def negativeTwistSectionsIsoStructure
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    Γ(sheafOfModules PS m, U) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, U) :=
  p3NegativeTwistSectionsIsoUnit K U i hU m ≪≫
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso U.topIso

/-- The twist trivialization by `X_i^m` commutes with restriction between
opens lying in the same coordinate chart. -/
theorem negativeTwistSectionsIsoStructure_natural
    (U V : Scheme.Opens (Proj PS)) (hVU : V ≤ U) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (sheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
      (negativeTwistSectionsIsoStructure K V i (hVU.trans hU) m).hom =
    (negativeTwistSectionsIsoStructure K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((AlgebraicGeometry.Proj PS).presheaf.map (homOfLE hVU).op) := by
  change (sheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
      ((p3NegativeTwistSectionsIsoUnit K V i (hVU.trans hU) m).hom ≫
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          V.topIso.hom) =
    ((p3NegativeTwistSectionsIsoUnit K U i hU m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom) ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        ((AlgebraicGeometry.Proj PS).presheaf.map (homOfLE hVU).op)
  rw [p3NegativeTwistSectionsIsoUnit_hom_topIso]
  rw [p3NegativeTwistSectionsIsoUnit_hom_topIso]
  exact ((Scheme.Modules.toPresheaf (Proj PS)).map
    (negativeTwistTrivializationHom K i m)).naturality (homOfLE hVU).op

lemma basicOpenIsoAway_inv_natural_addCommGrp
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) :
    let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    forgetRing.map ((AlgebraicGeometry.Proj PS).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op) ≫
      forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv =
    forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv ≫
      forgetRing.map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  dsimp only
  have h := congrArg
    (fun q => (forget₂ CommRingCat RingCat ⋙
      forget₂ RingCat AddCommGrpCat).map q)
    (basicOpenIsoAway_inv_natural K f g x d e hf hg hd hx)
  simpa only [Functor.map_comp] using h

lemma p3NegativeTwistBasicOpenIsoAway_hom
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    let U := AlgebraicGeometry.Proj.basicOpen PS f
    let hU : U ≤ p3StandardOpen (K := K) i :=
      AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
    let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    (p3NegativeTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom =
      (negativeTwistSectionsIsoStructure K U i hU m).hom ≫
        forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from `D₊(f)` to `D₊(fg)` is carried by the concrete twist
section isomorphisms to the canonical homogeneous-localization map. -/
theorem negativeTwistBasicOpenIsoAway_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    (sheafOfModules PS m).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (p3NegativeTwistBasicOpenIsoAway K x (d + e)
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
        (dvd_trans hdiv ⟨g, hx⟩) m).hom =
    (p3NegativeTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  let Uf := AlgebraicGeometry.Proj.basicOpen PS f
  let Ux := AlgebraicGeometry.Proj.basicOpen PS x
  let hxf : Ux ≤ Uf :=
    AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩
  let hfi : Uf ≤ p3StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
  let hxi : Ux ≤ p3StandardOpen (K := K) i := hxf.trans hfi
  let forgetRing := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let bx := forgetRing.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv
  let bf := forgetRing.map
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv
  let amap := forgetRing.map
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx))
  have hxHom := p3NegativeTwistBasicOpenIsoAway_hom K x (d + e)
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
    (dvd_trans hdiv ⟨g, hx⟩) m
  have hfHom := p3NegativeTwistBasicOpenIsoAway_hom K f d hf hd i hdiv m
  rw [hxHom, hfHom]
  have htwist := negativeTwistSectionsIsoStructure_natural K Uf Ux hxf i hfi m
  have haway := basicOpenIsoAway_inv_natural_addCommGrp
    K f g x d e hf hg hd hx
  change (sheafOfModules PS m).presheaf.map (homOfLE hxf).op ≫
      (negativeTwistSectionsIsoStructure K Ux i hxi m).hom ≫ bx =
    (negativeTwistSectionsIsoStructure K Uf i hfi m).hom ≫ bf ≫ amap
  rw [← Category.assoc, htwist]
  simp only [Category.assoc]
  rw [haway]

/-- The raw Cech complex of the concrete negative twist on the standard
four-coordinate cover. -/
def p3NegativeTwistCechComplex (m : ℕ) : CochainComplex AddCommGrpCat ℕ :=
  (CategoryTheory.cechComplexFunctor (p3StandardOpen (K := K))).obj
    (modulePresheaf 𝒮 m).presheaf

/-- The terms of the raw standard-cover Cech complex are products of
sections on all ordered finite intersections. -/
theorem p3NegativeTwistCechComplex_X (m n : ℕ) :
    (p3NegativeTwistCechComplex (K := K) m).X n =
      ∏ᶜ fun (i : Fin (n + 1) → Fin 4) =>
        (modulePresheaf 𝒮 m).presheaf.obj
          (op (∏ᶜ fun a : Fin (n + 1) =>
            p3StandardOpen (K := K) (i a))) := rfl

/-- A finite intersection of projective basic opens is the basic open of
the product of their defining elements. -/
theorem projective_basicOpen_finset_inf
    {ι : Type w} (s : Finset ι) (f : ι → S) :
    AlgebraicGeometry.Proj.basicOpen 𝒮 (∏ i ∈ s, f i) =
      s.inf (fun i => AlgebraicGeometry.Proj.basicOpen 𝒮 (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, ha, not_false_eq_true,
        Finset.inf_insert]
      rw [AlgebraicGeometry.Proj.basicOpen_mul, ih]

/-- The product of the coordinates indexing an ordered Cech intersection. -/
def p3CechDenominator (n : ℕ) (f : Fin (n + 1) → Fin 4) : S :=
  ∏ a, MvPolynomial.X (R := K) (f a)

/-- The denominator of an `n`-fold ordered intersection is homogeneous of
positive degree `n+1`. -/
theorem p3CechDenominator_mem (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    p3CechDenominator (K := K) n f ∈ PS (n + 1) := by
  simpa [p3CechDenominator] using MvPolynomial.IsHomogeneous.prod
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a)) (fun _ ↦ (1 : ℕ))
    (fun a _ ↦ MvPolynomial.isHomogeneous_X K (f a))

/-- The first coordinate in a nonempty ordered intersection divides its
coordinate product. -/
theorem p3Coordinate_zero_dvd_cechDenominator
    (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    MvPolynomial.X (R := K) (f 0) ∣ p3CechDenominator (K := K) n f := by
  simpa [p3CechDenominator] using
    (Finset.dvd_prod_of_mem
      (fun a : Fin (n + 1) ↦ MvPolynomial.X (R := K) (f a))
      (Finset.mem_univ (0 : Fin (n + 1))))

/-- An ordered standard-cover intersection is the basic open of the product
of its coordinate denominators. -/
theorem p3CechBasicOpen_eq_inf (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    AlgebraicGeometry.Proj.basicOpen PS
        (p3CechDenominator (K := K) n f) =
      ⨅ a, p3StandardOpen (K := K) (f a) := by
  change AlgebraicGeometry.Proj.basicOpen PS
      (∏ a, MvPolynomial.X (R := K) (f a)) =
    ⨅ a, AlgebraicGeometry.Proj.basicOpen PS
      (MvPolynomial.X (R := K) (f a))
  rw [← Finset.inf_univ_eq_iInf]
  simpa using projective_basicOpen_finset_inf (K := K)
    (Finset.univ : Finset (Fin (n + 1)))
    (fun a ↦ MvPolynomial.X (R := K) (f a))

/-- Every summand of the standard-cover Cech complex is explicitly the
degree-zero homogeneous localization at the product of its coordinates. -/
def p3NegativeTwistCechSummandIsoAway
    (m n : ℕ) (f : Fin (n + 1) → Fin 4) :
    Γ(sheafOfModules PS m,
        ⨅ a, p3StandardOpen (K := K) (f a)) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS
        (p3CechDenominator (K := K) n f)) :=
  (modulePresheaf PS m).presheaf.mapIso
      (eqToIso (p3CechBasicOpen_eq_inf (K := K) n f)).op ≪≫
    p3NegativeTwistBasicOpenIsoAway K
      (p3CechDenominator (K := K) n f) (n + 1)
      (p3CechDenominator_mem (K := K) n f) (Nat.succ_pos n)
      (f 0) (p3Coordinate_zero_dvd_cechDenominator (K := K) n f) m

/-- Every intersection in the Cech nerve of the standard coordinate cover
of projective three-space is affine. -/
theorem p3StandardOpen_cech_inter_affine
    (n : ℕ) (f : Fin (n + 1) → Fin 4) :
    AlgebraicGeometry.IsAffineOpen
      (⨅ i, p3StandardOpen (K := K) (f i)) := by
  classical
  change AlgebraicGeometry.IsAffineOpen
    (⨅ i, AlgebraicGeometry.Proj.basicOpen 𝒮
      (MvPolynomial.X (R := K) (f i)))
  rw [← Finset.inf_univ_eq_iInf,
    ← projective_basicOpen_finset_inf (K := K)]
  have hhom : MvPolynomial.IsHomogeneous
      (∏ i : Fin (n + 1), MvPolynomial.X (R := K) (f i)) (n + 1) := by
    simpa using MvPolynomial.IsHomogeneous.prod
      (Finset.univ : Finset (Fin (n + 1)))
      (fun i => MvPolynomial.X (R := K) (f i)) (fun _ => (1 : ℕ))
      (fun i _ => MvPolynomial.isHomogeneous_X K (f i))
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒮
    (∏ i : Fin (n + 1), MvPolynomial.X (R := K) (f i))
    (m := n + 1) hhom (Nat.succ_pos n)


/-! ### Exactness at the augmented degree-zero Cech term -/

/-- A universe-lifted copy of the four coordinate indices, used by the
 equalizer-products form of the sheaf condition. -/
abbrev P3CoordinateIndex := ULift.{u} (Fin 4)

/-- The standard coordinate cover with its index in the ambient universe. -/
def p3StandardOpenLifted (i : P3CoordinateIndex) :
    Scheme.Opens (Proj PS) :=
  p3StandardOpen (K := K) i.down

/-- The lifted standard coordinate family still covers projective space. -/
theorem p3StandardOpenLifted_iSup :
    ⨆ i : P3CoordinateIndex, p3StandardOpenLifted (K := K) i = ⊤ := by
  simpa [p3StandardOpenLifted] using p3StandardOpen_iSup K

namespace P3CechZero

/-- The equalizer fork that expresses gluing over the four standard opens. -/
def gluingFork (m : ℕ) :=
  TopCat.Presheaf.SheafConditionEqualizerProducts.fork
    (modulePresheaf PS m).presheaf (p3StandardOpenLifted (K := K))

/-- The sheaf condition makes the standard-cover gluing fork a limit. -/
def forkIsLimit (m : ℕ) : IsLimit (gluingFork (K := K) m) := by
  exact ((TopCat.Presheaf.isSheaf_iff_isSheafEqualizerProducts
    (modulePresheaf PS m).presheaf).mp
      (sheafOfModules PS m).isSheaf
      (p3StandardOpenLifted (K := K))).some

/-- Global sections, sections on single standard opens, and sections on
pairwise intersections form the augmented degree-zero Cech short complex. -/
def shortComplex (m : ℕ) : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk
    (TopCat.Presheaf.SheafConditionEqualizerProducts.res
      (modulePresheaf PS m).presheaf (p3StandardOpenLifted (K := K)))
    (TopCat.Presheaf.SheafConditionEqualizerProducts.leftRes
        (modulePresheaf PS m).presheaf
        (p3StandardOpenLifted (K := K)) -
      TopCat.Presheaf.SheafConditionEqualizerProducts.rightRes
        (modulePresheaf PS m).presheaf
        (p3StandardOpenLifted (K := K)))
    (by
      rw [Preadditive.comp_sub,
        TopCat.Presheaf.SheafConditionEqualizerProducts.w, sub_self])

/-- Because the four opens cover, the augmentation starts at actual global
sections over the top open. -/
theorem shortComplex_X₁_eq_top (m : ℕ) :
    (shortComplex (K := K) m).X₁ =
      (modulePresheaf PS m).presheaf.obj
        (op (⊤ : Scheme.Opens (Proj PS))) := by
  change (modulePresheaf PS m).presheaf.obj
    (op (⨆ i, p3StandardOpenLifted (K := K) i)) = _
  rw [p3StandardOpenLifted_iSup]

/-- Exactness at the product of sections over individual coordinate opens
is an immediate consequence of the sheaf gluing condition. -/
theorem shortComplex_exact (m : ℕ) :
    (shortComplex (K := K) m).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  exact Preadditive.isLimitKernelForkOfFork (forkIsLimit (K := K) m)

end P3CechZero

end ProjectiveNegativeTwist
end PfaffianDescent
