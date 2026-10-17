import PfaffianDescent.ProjectivePositiveTwist
import PfaffianDescent.VoisinProjectiveSpaceCech

/-!
# Local triviality of the positive projective twist

This promotes the positive-twist stalk calculation to the standard projective
basic opens.  It is the local ingredient needed to make the positive and
negative twists into inverse tensor factors in Voisin's Serre construction.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Positive homogeneous multiplication becomes an isomorphism after
restriction to the basic open on which its homogeneous multiplier is
invertible. -/
theorem restrict_positiveMulHomogeneous_isIso_on_basicOpen {d : ℕ}
    (s : 𝒜 d) (m : ℕ)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    IsIso ((Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).map
        (positiveMulHomogeneous 𝒜 s m)) := by
  let U := homogeneousBasicOpen 𝒜 (s : A)
  apply restrict_map_isIso_of_stalk U
  intro x
  letI : (positivePointIdeal 𝒜 (U.ι x)).IsPrime :=
    ProjectiveSpectrum.isPrime (U.ι x)
  have hsx : (s : A) ∈ (positivePointIdeal 𝒜 (U.ι x)).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact (ProjectiveSpectrum.mem_basicOpen 𝒜 (s : A) (U.ι x)).mp x.property
  change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
    (positiveMulHomogeneousPresheaf 𝒜 s m))
  exact positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    𝒜 s m (U.ι x) hsx hspan

/-- The explicit local isomorphism supplied by positive homogeneous
multiplication on its projective basic open. -/
noncomputable def restrictPositiveMulHomogeneousIso_on_basicOpen {d : ℕ}
    (s : 𝒜 d) (m : ℕ)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).obj
        (positiveSheafOfModules 𝒜 m) ≅
      (Scheme.Modules.restrictFunctor
        (homogeneousBasicOpen 𝒜 (s : A)).ι).obj
        (positiveSheafOfModules 𝒜 (m + d)) := by
  letI : IsIso ((Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).map
        (positiveMulHomogeneous 𝒜 s m)) :=
    restrict_positiveMulHomogeneous_isIso_on_basicOpen 𝒜 s m hspan
  exact asIso ((Scheme.Modules.restrictFunctor
    (homogeneousBasicOpen 𝒜 (s : A)).ι).map
      (positiveMulHomogeneous 𝒜 s m))

/-- On the basic open where a degree-`d` multiplier is invertible, the
positive `d`-twist is an actual trivial module sheaf. -/
noncomputable def restrictPositiveTwistUnitIso_on_basicOpen {d : ℕ}
    (s : 𝒜 d)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    (Scheme.Modules.restrictFunctor
      (homogeneousBasicOpen 𝒜 (s : A)).ι).obj
        (positiveSheafOfModules 𝒜 d) ≅
      SheafOfModules.unit
        ((homogeneousBasicOpen 𝒜 (s : A) : Scheme).ringCatSheaf) := by
  let F := Scheme.Modules.restrictFunctor
    (homogeneousBasicOpen 𝒜 (s : A)).ι
  simpa only [zero_add] using
    ((restrictPositiveMulHomogeneousIso_on_basicOpen 𝒜 s 0 hspan).symm ≪≫
      F.mapIso (positiveZeroTwistIso 𝒜) ≪≫
      F.mapIso (unitIsoZeroTwist 𝒜).symm ≪≫
      Scheme.Modules.restrictUnitIso
        (homogeneousBasicOpen 𝒜 (s : A)).ι)

/-- A local unit isomorphism after restriction along an open immersion
transports canonically to the module category on the corresponding over-site.
This is the form required by the tensor-exactness machinery. -/
noncomputable def overFunctorIsoUnit_of_restrictIsoUnit
    {X : Scheme.{u}} (U : X.Opens) {T : X.Modules}
    (e : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf
        (PfaffianDescent.SheafOfModules.commRingSheafOver X.sheaf U)) := by
  let E := Scheme.Modules.overEquiv U
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let n := Scheme.Modules.overFunctorEquiv U
  let eUnitOver := PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U
    (Iso.refl (SheafOfModules.unit X.ringCatSheaf))
  let uIso : E.functor.obj
      (SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf
        (PfaffianDescent.SheafOfModules.commRingSheafOver X.sheaf U))) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (E.functor.mapIso eUnitOver).symm ≪≫
      n.app (SheafOfModules.unit X.ringCatSheaf) ≪≫
      Scheme.Modules.restrictUnitIso U.ι
  let eE : E.functor.obj (H.obj T) ≅ E.functor.obj
      (SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf
        (PfaffianDescent.SheafOfModules.commRingSheafOver X.sheaf U))) :=
    n.app T ≪≫ e ≪≫ uIso.symm
  exact (E.unitIso.app (H.obj T)) ≪≫ E.inverse.mapIso eE ≪≫
    (E.unitIso.app
      (SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf
        (PfaffianDescent.SheafOfModules.commRingSheafOver X.sheaf U)))).symm

/-- The positive degree-`d` twist is the unit module on the over-site of the
basic open `D₊(s)`. -/
noncomputable def overFunctorPositiveTwistUnitIso_on_basicOpen {d : ℕ}
    (s : 𝒜 d)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    (SheafOfModules.overFunctor (Proj 𝒜).ringCatSheaf
      (homogeneousBasicOpen 𝒜 (s : A))).obj
        (positiveSheafOfModules 𝒜 d) ≅
      SheafOfModules.unit (PfaffianDescent.SheafOfModules.commRingSheafToRingSheaf
        (PfaffianDescent.SheafOfModules.commRingSheafOver
          (Proj 𝒜).sheaf (homogeneousBasicOpen 𝒜 (s : A)))) :=
  overFunctorIsoUnit_of_restrictIsoUnit
    (homogeneousBasicOpen 𝒜 (s : A))
    (restrictPositiveTwistUnitIso_on_basicOpen 𝒜 s hspan)

set_option backward.isDefEq.respectTransparency false in
/-- At degree zero, the pairing agrees after the canonical unit-to-zero-twist
map with the ordinary right-unit map followed by the zero-twist comparison. -/
theorem positiveNegativePairing_zero_factorization :
    schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 0)) (unitToZeroTwist 𝒜) ≫
      positiveNegativePairing 𝒜 0 =
    (schemeModuleTensorUnitRightIso (positiveSheafOfModules 𝒜 0)).hom ≫
      positiveZeroToZeroTwist 𝒜 := by
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  rw [schemeModuleTensorMap_eq_sheafification]
  erw [adj.homEquiv_naturality_left]
  have hpair : adj.homEquiv
      (PresheafOfModules.Monoidal.tensorObj (positiveSheafOfModules 𝒜 0).val
        (sheafOfModules 𝒜 0).val) (sheafOfModules 𝒜 0)
      (positiveNegativePairing 𝒜 0) = positiveNegativePairingPresheaf 𝒜 0 := by
    exact (adj.homEquiv _ _).apply_symm_apply _
  rw [hpair]
  unfold schemeModuleTensorUnitRightIso
  change _ = adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 (Proj 𝒜).ringCatSheaf.obj)).map
      (schemeModuleTensorUnitRightRawIso (positiveSheafOfModules 𝒜 0)).hom ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Proj 𝒜).ringCatSheaf.obj)).counit.app
          (positiveSheafOfModules 𝒜 0) ≫ positiveZeroToZeroTwist 𝒜)
  erw [adj.homEquiv_naturality_left]
  rw [schemeModuleSheafificationHomEquiv_counit_comp]
  ext1 U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro p q
  apply Subtype.ext
  funext x
  change p.1 x * (q.1 x).val = (q.1 x).val * p.1 x
  ring

/-- The degree-zero positive/negative pairing is an isomorphism. -/
theorem positiveNegativePairing_zero_isIso : IsIso (positiveNegativePairing 𝒜 0) := by
  let e := unitIsoZeroTwist 𝒜
  let a := schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 0)) e.hom
  let b := (schemeModuleTensorUnitRightIso (positiveSheafOfModules 𝒜 0)).hom ≫
    positiveZeroToZeroTwist 𝒜
  have ha : IsIso a := by
    change IsIso (schemeModuleTensorMap (𝟙 (positiveSheafOfModules 𝒜 0)) e.hom)
    exact (schemeModuleTensorMapIso (Iso.refl _) e).isIso_hom
  have hb : IsIso b := by
    letI : IsIso (positiveZeroToZeroTwist 𝒜) :=
      (positiveZeroTwistIso 𝒜).isIso_hom
    infer_instance
  exact IsIso.of_isIso_fac_left (f := a) (g := positiveNegativePairing 𝒜 0)
    (h := b) (positiveNegativePairing_zero_factorization 𝒜)

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K]

local notation "S" => MvPolynomial (Fin 4) K
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The local top-section component of a restricted sheaf morphism is its
ambient component conjugated by the two restriction identifications. -/
lemma moduleRestrictTopIso_local_map
    {M N : (Proj PS).Modules} (t : M ⟶ N)
    (U : Scheme.Opens (Proj PS)) :
    ((Scheme.Modules.toPresheaf (U : Scheme)).map
      ((Scheme.Modules.restrictFunctor U.ι).map t)).app (op ⊤) =
      (moduleRestrictTopIso M U).hom ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map t).app (op U) ≫
        (moduleRestrictTopIso N U).inv := by
  rw [moduleRestrictTopIso_naturality t U]
  simp

lemma schemeModulesToPresheaf_map_comp_app
    {U : Scheme} {M N P : U.Modules} (g : M ⟶ N) (h : N ⟶ P)
    (V : (Scheme.Opens U)ᵒᵖ) :
    ((Scheme.Modules.toPresheaf U).map (g ≫ h)).app V =
      ((Scheme.Modules.toPresheaf U).map g).app V ≫
        ((Scheme.Modules.toPresheaf U).map h).app V := by
  exact congrArg (fun q ↦ q.app V)
    ((Scheme.Modules.toPresheaf U).map_comp g h)

lemma cancel_three_iso_conjugations
    {C : Type*} [Category C]
    {A B C₀ D E F G H I : C}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : C₀ ⟶ D)
    (e₁ : E ≅ D) (d : D ⟶ F) (e₂ : G ≅ F)
    (g : F ⟶ H) (e₃ : I ≅ H) (q : A ⟶ C₀)
    (hab : a ≫ b = q) :
    a ≫ b ≫ c ≫ e₁.inv ≫ e₁.hom ≫ d ≫ e₂.inv ≫
      e₂.hom ≫ g ≫ e₃.inv ≫ e₃.hom =
        q ≫ c ≫ d ≫ g := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [e₃.inv_hom_id, Category.comp_id, ← Category.assoc, hab]

/-- The equality transport from degree `0 + m` to degree `m` leaves the
underlying positive homogeneous fraction unchanged. -/
lemma positiveZeroAddCast_apply_val
    (m : ℕ) (U : (Scheme.Opens (Proj PS))ᵒᵖ)
    (z : (positiveSheafOfModules PS (0 + m)).val.obj U)
    (x : U.unop) :
    (((eqToIso (by rw [zero_add]) :
      positiveSheafOfModules PS (0 + m) ≅
        positiveSheafOfModules PS m).hom.val.app U z).1 x) = z.1 x := by
  let p : positiveSheafOfModules PS (0 + m) =
      positiveSheafOfModules PS m :=
    congrArg (positiveSheafOfModules PS) (Nat.zero_add m)
  change ((((eqToHom p : positiveSheafOfModules PS (0 + m) ⟶
      positiveSheafOfModules PS m).val.app U) z).1 x) = z.1 x
  have h :
      (((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom p)).app U z) ≍ z := by
    have hmor :
        (eqToHom p : positiveSheafOfModules PS (0 + m) ⟶
          positiveSheafOfModules PS m) ≍
          𝟙 (positiveSheafOfModules PS (0 + m)) :=
      eqToHom_heq_id_dom _ _ _
    have happ :
        ((Scheme.Modules.toPresheaf (Proj PS)).map (eqToHom p)).app U ≍
          ((Scheme.Modules.toPresheaf (Proj PS)).map
            (𝟙 (positiveSheafOfModules PS (0 + m)))).app U := by
      congr <;> exact (Nat.zero_add m).symm
    have hout :
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (eqToHom p)).app U) z ≍
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (𝟙 (positiveSheafOfModules PS (0 + m)))).app U) z := by
      congr <;> simp only [Nat.zero_add]
    have hid :
        (((Scheme.Modules.toPresheaf (Proj PS)).map
          (𝟙 (positiveSheafOfModules PS (0 + m)))).app U) z = z := by
      rfl
    exact hout.trans (heq_of_eq hid)
  have hcoe :
      (((((Scheme.Modules.toPresheaf (Proj PS)).map
        (eqToHom p)).app U) z).1) = z.1 :=
    (Subtype.heq_iff_coe_eq (fun q => by simp only [zero_add])).mp h
  exact congrFun hcoe x

/-- Pulling a function on an open subscheme back through the restricted-unit
isomorphism and then returning to ambient sections is the ordinary top-open
identification. -/
lemma restrictUnit_inv_comp_moduleRestrictTop
    (U : Scheme.Opens (Proj PS)) :
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      (Scheme.Modules.restrictUnitIso U.ι).inv).app (op ⊤)) ≫
      (moduleRestrictTopIso
        (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        U.topIso.hom := by
  let e := ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso
    (Scheme.Modules.restrictUnitIso U.ι)).app (op ⊤)
  have h := restrictUnit_app_top_topIso K U
  change e.inv ≫
      (moduleRestrictTopIso
        (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom = _
  rw [← h]
  change e.inv ≫ e.hom ≫ _ = _
  exact e.inv_hom_id_assoc _

/-- The positive `m`-twist is the unit module on any open contained in a
standard coordinate chart.  This form is needed on pairwise chart
intersections when comparing the four Laurent representatives. -/
noncomputable def p3PositiveTwistOpenIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).obj (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let s := degreeOnePower PS (p3Coordinate K i) m
  let f₀ := positiveMulHomogeneous PS s 0
  let e : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    f₀ ≫ e.hom
  have hf₀ : IsIso (R.map f₀) := by
    dsimp only [f₀, s]
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hXi : (MvPolynomial.X i : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS
        (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
    have hsx : (degreeOnePower PS (p3Coordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (p3Coordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (p3Coordinate K i) m) 0 (U.ι x) hsx
    exact (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨p3Coordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  exact (asIso (R.map f)).symm ≪≫
    R.mapIso (positiveZeroTwistIso PS) ≪≫
    (R.mapIso (unitIsoZeroTwist PS)).symm ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- The positive `m`-twist on projective three-space is the unit module on
each standard coordinate chart. -/
noncomputable def p3PositiveTwistStandardOpenIsoUnit
    (i : Fin 4) (m : ℕ) (hm : 0 < m) :
    (Scheme.Modules.restrictFunctor
      (p3StandardOpen (K := K) i).ι).obj (positiveSheafOfModules PS m) ≅
      SheafOfModules.unit
        (p3StandardOpen (K := K) i : Scheme).ringCatSheaf := by
  exact p3PositiveTwistOpenIsoUnit K (p3StandardOpen (K := K) i) i le_rfl m

/-- Sections of the positive twist on an open contained in `D₊(X_i)` are
identified with regular functions on that open by division by `X_i^m`. -/
noncomputable def p3PositiveTwistSectionsIsoUnit
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      AddCommGrpCat.of Γ((U : Scheme), ⊤) := by
  let e := p3PositiveTwistOpenIsoUnit K U i hU m
  exact (moduleRestrictTopIso (positiveSheafOfModules PS m) U).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)

lemma p3PositiveTwistSectionsIsoUnit_inv_decompose
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    let e := p3PositiveTwistOpenIsoUnit K U i hU m
    (p3PositiveTwistSectionsIsoUnit K U i hU m).inv =
      (((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤)).inv ≫
        (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom := by
  dsimp only
  rfl

/-- The inverse chart trivialization is literal multiplication by `X_i^m`
after the ordinary structure-function and degree-zero identifications. -/
lemma p3PositiveTwistSectionsIsoUnit_inv
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    let a := degreeOnePower PS (p3Coordinate K i) m
    let eadd : positiveSheafOfModules PS (0 + m) ≅
        positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
    let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
      positiveMulHomogeneous PS a 0 ≫ eadd.hom
    (p3PositiveTwistSectionsIsoUnit K U i hU m).inv =
      F.map U.topIso.hom ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (unitToZeroTwist PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map
          (zeroTwistToPositiveZero PS)).app (op U) ≫
        ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U) := by
  dsimp only
  let R := Scheme.Modules.restrictFunctor U.ι
  let a := degreeOnePower PS (p3Coordinate K i) m
  let f₀ := positiveMulHomogeneous PS a 0
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    f₀ ≫ eadd.hom
  have hf₀ : IsIso (R.map f₀) := by
    dsimp only [f₀, a]
    apply restrict_map_isIso_of_stalk U
    intro x
    letI : (positivePointIdeal PS (U.ι x)).IsPrime :=
      ProjectiveSpectrum.isPrime (U.ι x)
    have hXi : (MvPolynomial.X i : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact (ProjectiveSpectrum.mem_basicOpen PS
        (MvPolynomial.X i) (U.ι x)).mp (hU x.property)
    have hsx : (degreeOnePower PS (p3Coordinate K i) m : S) ∈
        (positivePointIdeal PS (U.ι x)).primeCompl := by
      change (MvPolynomial.X i : S) ^ m ∈
        (positivePointIdeal PS (U.ι x)).primeCompl
      exact Submonoid.pow_mem _ hXi m
    change IsIso ((TopCat.Presheaf.stalkFunctor _ (U.ι x)).map
      (positiveMulHomogeneousPresheaf PS
        (degreeOnePower PS (p3Coordinate K i) m) 0))
    apply positiveMulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
      PS (degreeOnePower PS (p3Coordinate K i) m) 0 (U.ι x) hsx
    exact (p3Coordinates_span_irrelevant K).trans (Ideal.span_mono (by
      rintro _ ⟨j, rfl⟩
      exact ⟨p3Coordinate K j, rfl⟩))
  letI : IsIso (R.map f₀) := hf₀
  letI : IsIso (R.map f) := by
    dsimp only [f]
    rw [R.map_comp]
    infer_instance
  rw [p3PositiveTwistSectionsIsoUnit_inv_decompose K U i hU m]
  let e := p3PositiveTwistOpenIsoUnit K U i hU m
  change ((Scheme.Modules.toPresheaf (U : Scheme)).map e.inv).app (op ⊤) ≫
      (moduleRestrictTopIso (positiveSheafOfModules PS m) U).hom = _
  have heinv : e.inv =
      (((Scheme.Modules.restrictUnitIso U.ι).inv ≫
          R.map (unitIsoZeroTwist PS).hom) ≫
        R.map (positiveZeroTwistIso PS).inv) ≫ R.map f := by
    dsimp only [e, p3PositiveTwistOpenIsoUnit]
    rfl
  rw [heinv]
  rw [schemeModulesToPresheaf_map_comp_app
    (((Scheme.Modules.restrictUnitIso U.ι).inv ≫
      R.map (unitIsoZeroTwist PS).hom) ≫
      R.map (positiveZeroTwistIso PS).inv) (R.map f) (op ⊤),
    schemeModulesToPresheaf_map_comp_app
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        R.map (unitIsoZeroTwist PS).hom)
      (R.map (positiveZeroTwistIso PS).inv) (op ⊤),
    schemeModulesToPresheaf_map_comp_app
      (Scheme.Modules.restrictUnitIso U.ι).inv
      (R.map (unitIsoZeroTwist PS).hom) (op ⊤)]
  have hunit : (unitIsoZeroTwist PS).hom = unitToZeroTwist PS := by
    dsimp only [unitIsoZeroTwist]
    rfl
  have hzero : (positiveZeroTwistIso PS).inv =
      zeroTwistToPositiveZero PS := rfl
  rw [hunit, hzero]
  rw [moduleRestrictTopIso_local_map K (unitToZeroTwist PS) U,
    moduleRestrictTopIso_local_map K (zeroTwistToPositiveZero PS) U,
    moduleRestrictTopIso_local_map K f U]
  exact cancel_three_iso_conjugations
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
      (Scheme.Modules.restrictUnitIso U.ι).inv).app (op ⊤))
    (moduleRestrictTopIso
      (SheafOfModules.unit (Proj PS).ringCatSheaf) U).hom
    (((Scheme.Modules.toPresheaf (Proj PS)).map
      (unitToZeroTwist PS)).app (op U))
    (moduleRestrictTopIso (sheafOfModules PS 0) U)
    (((Scheme.Modules.toPresheaf (Proj PS)).map
      (zeroTwistToPositiveZero PS)).app (op U))
    (moduleRestrictTopIso (positiveSheafOfModules PS 0) U)
    (((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U))
    (moduleRestrictTopIso (positiveSheafOfModules PS m) U)
    ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
      U.topIso.hom)
    (restrictUnit_inv_comp_moduleRestrictTop K U)

/-- Pointwise, the inverse of the positive chart trivialization multiplies
the chart function by `X_i^m`. -/
lemma p3PositiveTwistSectionsIsoUnit_inv_apply_val
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ)
    (r : Γ((U : Scheme), ⊤)) (x : U) :
    ((p3PositiveTwistSectionsIsoUnit K U i hU m).inv r).1 x =
      algebraMap S (PositiveFiber PS x.1)
          ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) *
        ((((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          U.topIso.hom) r).1 x).val := by
  rw [p3PositiveTwistSectionsIsoUnit_inv K U i hU m]
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let q := F.map U.topIso.hom r
  let z₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (unitToZeroTwist PS)).app (op U) q
  let p₀ := ((Scheme.Modules.toPresheaf (Proj PS)).map
    (zeroTwistToPositiveZero PS)).app (op U) z₀
  let zm := (positiveMulHomogeneous PS
    (degreeOnePower PS (p3Coordinate K i) m) 0).val.app (op U) p₀
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  change (((eadd.hom.val.app (op U)) zm).1 x) = _
  rw [positiveZeroAddCast_apply_val K m (op U) zm x]
  change algebraMap S (PositiveFiber PS x.1)
      ((degreeOnePower PS (p3Coordinate K i) m : PS m) : S) * p₀.1 x = _
  rfl

/-- The positive chart trivialization with its values transported to ambient
structure-sheaf sections on the same open. -/
noncomputable def p3PositiveTwistSectionsIsoStructure
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    Γ(positiveSheafOfModules PS m, U) ≅
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).obj
        Γ(Proj PS, U) :=
  p3PositiveTwistSectionsIsoUnit K U i hU m ≪≫
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).mapIso U.topIso

/-- The single ambient sheaf morphism whose local components are the
inverses of all positive chart trivializations for the coordinate `X_i`. -/
noncomputable def p3PositiveTwistTrivializationInvHom
    (i : Fin 4) (m : ℕ) :
    SheafOfModules.unit (Proj PS).ringCatSheaf ⟶
      positiveSheafOfModules PS m :=
  let a := degreeOnePower PS (p3Coordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS ≫
    (positiveMulHomogeneous PS a 0 ≫ eadd.hom)

/-- The inverse positive chart is the component of one ambient sheaf
morphism; in particular it is compatible with every restriction map. -/
lemma p3PositiveTwistSectionsIsoStructure_inv
    (U : Scheme.Opens (Proj PS)) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (p3PositiveTwistSectionsIsoStructure K U i hU m).inv =
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (p3PositiveTwistTrivializationInvHom K i m)).app (op U) := by
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let a := degreeOnePower PS (p3Coordinate K i) m
  let eadd : positiveSheafOfModules PS (0 + m) ≅
      positiveSheafOfModules PS m := eqToIso (by rw [zero_add])
  let f : positiveSheafOfModules PS 0 ⟶ positiveSheafOfModules PS m :=
    positiveMulHomogeneous PS a 0 ≫ eadd.hom
  change F.map U.topIso.inv ≫
      (p3PositiveTwistSectionsIsoUnit K U i hU m).inv = _
  rw [p3PositiveTwistSectionsIsoUnit_inv K U i hU m]
  change F.map U.topIso.inv ≫
      F.map U.topIso.hom ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (unitToZeroTwist PS)).app (op U) ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map
        (zeroTwistToPositiveZero PS)).app (op U) ≫
      ((Scheme.Modules.toPresheaf (Proj PS)).map f).app (op U) = _
  rw [← Category.assoc, ← F.map_comp]
  simp only [Iso.inv_hom_id, Functor.map_id, Category.id_comp]
  change _ = ((Scheme.Modules.toPresheaf (Proj PS)).map
    ((unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS) ≫ f)).app (op U)
  rw [schemeModulesToPresheaf_map_comp_app
      (unitToZeroTwist PS ≫ zeroTwistToPositiveZero PS) f (op U),
    schemeModulesToPresheaf_map_comp_app
      (unitToZeroTwist PS) (zeroTwistToPositiveZero PS) (op U)]
  dsimp only [f]
  rw [schemeModulesToPresheaf_map_comp_app
    (positiveMulHomogeneous PS a 0) eadd.hom (op U)]
  simp
  rfl

/-- Positive chart trivializations commute with restriction between opens in
the same coordinate chart. -/
lemma p3PositiveTwistSectionsIsoStructure_natural
    (U V : Scheme.Opens (Proj PS)) (hVU : V ≤ U) (i : Fin 4)
    (hU : U ≤ p3StandardOpen (K := K) i) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op ≫
        (p3PositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m).hom =
      (p3PositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
          ((Proj PS).presheaf.map (homOfLE hVU).op) := by
  let eU := p3PositiveTwistSectionsIsoStructure K U i hU m
  let eV := p3PositiveTwistSectionsIsoStructure K V i (hVU.trans hU) m
  let rP := (positiveSheafOfModules PS m).presheaf.map (homOfLE hVU).op
  let rO := (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
    ((Proj PS).presheaf.map (homOfLE hVU).op)
  have hinv : rO ≫ eV.inv = eU.inv ≫ rP := by
    rw [p3PositiveTwistSectionsIsoStructure_inv K,
      p3PositiveTwistSectionsIsoStructure_inv K]
    exact ((Scheme.Modules.toPresheaf (Proj PS)).map
      (p3PositiveTwistTrivializationInvHom K i m)).naturality (homOfLE hVU).op
  apply (cancel_mono eV.inv).mp
  change (rP ≫ eV.hom) ≫ eV.inv = (eU.hom ≫ rO) ≫ eV.inv
  simp only [Category.assoc, eV.hom_inv_id, Category.comp_id]
  rw [hinv]
  simp

/-- On a homogeneous basic open contained in `D₊(X_i)`, positive-twist
sections are degree-zero homogeneous localizations after division by the
chart basis `X_i^m`. -/
noncomputable def p3PositiveTwistBasicOpenIsoAway
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    Γ(positiveSheafOfModules PS m,
        AlgebraicGeometry.Proj.basicOpen PS f) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS f) := by
  let U := AlgebraicGeometry.Proj.basicOpen PS f
  have hU : U ≤ p3StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS
      (MvPolynomial.X i) f hdiv
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  exact p3PositiveTwistSectionsIsoUnit K U i hU m ≪≫
    F.mapIso U.topIso ≪≫
    F.mapIso (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).symm

lemma p3PositiveTwistBasicOpenIsoAway_hom
    (f : S) (d : ℕ) (hf : f ∈ PS d) (hd : 0 < d)
    (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    let U := AlgebraicGeometry.Proj.basicOpen PS f
    let hU : U ≤ p3StandardOpen (K := K) i :=
      AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
    let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
    (p3PositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom =
      (p3PositiveTwistSectionsIsoStructure K U i hU m).hom ≫
        F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restriction from `D₊(f)` to `D₊(fg)` is carried by the positive chart
coordinates to the canonical map of homogeneous localizations. -/
theorem positiveTwistBasicOpenIsoAway_natural
    (f g x : S) (d e : ℕ)
    (hf : f ∈ PS d) (hg : g ∈ PS e) (hd : 0 < d)
    (hx : x = f * g) (i : Fin 4) (hdiv : MvPolynomial.X i ∣ f) (m : ℕ) :
    (positiveSheafOfModules PS m).presheaf.map
        (homOfLE (AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩)).op ≫
      (p3PositiveTwistBasicOpenIsoAway K x (d + e)
        (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e) i
        (dvd_trans hdiv ⟨g, hx⟩) m).hom =
    (p3PositiveTwistBasicOpenIsoAway K f d hf hd i hdiv m).hom ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat).map
        (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx)) := by
  let Uf := AlgebraicGeometry.Proj.basicOpen PS f
  let Ux := AlgebraicGeometry.Proj.basicOpen PS x
  let hxf : Ux ≤ Uf :=
    AlgebraicGeometry.Proj.basicOpen_mono PS f x ⟨g, hx⟩
  let hfi : Uf ≤ p3StandardOpen (K := K) i :=
    AlgebraicGeometry.Proj.basicOpen_mono PS (MvPolynomial.X i) f hdiv
  let hxi : Ux ≤ p3StandardOpen (K := K) i := hxf.trans hfi
  let F := forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat
  let bx := F.map (AlgebraicGeometry.Proj.basicOpenIsoAway PS x
    (hx ▸ SetLike.mul_mem_graded hf hg) (Nat.add_pos_left hd e)).inv
  let bf := F.map
    (AlgebraicGeometry.Proj.basicOpenIsoAway PS f hf hd).inv
  let amap := F.map
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap PS hg hx))
  rw [p3PositiveTwistBasicOpenIsoAway_hom K,
    p3PositiveTwistBasicOpenIsoAway_hom K]
  have htwist := p3PositiveTwistSectionsIsoStructure_natural
    K Uf Ux hxf i hfi m
  have haway := basicOpenIsoAway_inv_natural_addCommGrp
    K f g x d e hf hg hd hx
  change (positiveSheafOfModules PS m).presheaf.map (homOfLE hxf).op ≫
      (p3PositiveTwistSectionsIsoStructure K Ux i hxi m).hom ≫ bx =
    (p3PositiveTwistSectionsIsoStructure K Uf i hfi m).hom ≫ bf ≫ amap
  rw [← Category.assoc, htwist]
  simp only [Category.assoc]
  rw [haway]

/-- Sections of the positive twist on a standard coordinate chart are
identified with sections of the structure sheaf on that chart.  Concretely,
the trivialization divides a degree-`m` section by `X_i^m`. -/
noncomputable def p3PositiveTwistStandardOpenSectionsIsoUnit
    (i : Fin 4) (m : ℕ) (hm : 0 < m) :
    Γ(positiveSheafOfModules PS m, p3StandardOpen (K := K) i) ≅
      AddCommGrpCat.of Γ((p3StandardOpen (K := K) i : Scheme), ⊤) := by
  exact p3PositiveTwistSectionsIsoUnit K
    (p3StandardOpen (K := K) i) i le_rfl m

/-- On `D₊(X_i)`, sections of `O(m)` are degree-zero elements of the
homogeneous localization at `X_i`; the `O(m)` grading is accounted for by
the chart basis `X_i^m`. -/
noncomputable def p3PositiveTwistStandardOpenIsoAway
    (i : Fin 4) (m : ℕ) (hm : 0 < m) :
    Γ(positiveSheafOfModules PS m, p3StandardOpen (K := K) i) ≅
      AddCommGrpCat.of (HomogeneousLocalization.Away PS (MvPolynomial.X i)) := by
  let U := p3StandardOpen (K := K) i
  exact p3PositiveTwistBasicOpenIsoAway K (MvPolynomial.X i) 1
    (MvPolynomial.isHomogeneous_X K i) (by decide) i (dvd_refl _) m

/-- The four standard coordinate opens form a covering family in the form
used by local tensor exactness. -/
theorem p3StandardOpenLifted_coversTop :
    (Opens.grothendieckTopology (Proj PS)).CoversTop
      (p3StandardOpenLifted (K := K)) := by
  rw [Opens.coversTop_iff]
  simpa only [TopologicalSpace.IsOpenCover] using
    p3StandardOpenLifted_iSup K

/-- Tensoring by the positive `m`-twist of projective three-space preserves
finite limits; its proof uses the explicit standard-open local units. -/
theorem p3PositiveTwist_tensorRight_preservesFiniteLimits
    (m : ℕ) (hm : 0 < m) :
    PreservesFiniteLimits (schemeModuleTensorRight (positiveSheafOfModules PS m)) := by
  apply schemeModuleTensorRight_preservesFiniteLimits_of_coversTop_iso_unit
    (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
  intro i
  exact overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) i.down)
    (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)

/-- Tensoring by the positive `m`-twist of projective three-space preserves
finite colimits for the same local-triviality reason. -/
theorem p3PositiveTwist_tensorRight_preservesFiniteColimits
    (m : ℕ) (hm : 0 < m) :
    PreservesFiniteColimits (schemeModuleTensorRight (positiveSheafOfModules PS m)) := by
  apply schemeModuleTensorRight_preservesFiniteColimits_of_coversTop_iso_unit
    (p3StandardOpenLifted (K := K)) (p3StandardOpenLifted_coversTop K)
  intro i
  exact overFunctorIsoUnit_of_restrictIsoUnit (p3StandardOpen (K := K) i.down)
    (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)

end ProjectiveNegativeTwist
end PfaffianDescent
