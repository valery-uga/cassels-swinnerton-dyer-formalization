import PfaffianDescent.VoisinHypersurfaceRestriction
import PfaffianDescent.VoisinSheafStalk
import PfaffianDescent.ClosedImmersionPushforwardExact

/-!
# Cokernel of a projective hypersurface equation

This file transports the homogeneous-localization calculation for a
projective hypersurface to the categorical stalks of its pushed-forward
structure sheaf.
-/

noncomputable section

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace TopCat Topology

universe u

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- After identifying the stalk of the unit module with the structure-ring
stalk and the stalk of a pushforward at an image point with the source stalk,
the module map `O_Y -> f_* O_X` is the ordinary scheme-theoretic stalk map. -/
theorem closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∀ r : Y.presheaf.stalk (f x),
      (presheafOfModules_unitStalkLinearEquiv X.presheaf x).symm
        (TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
          (closedImmersionPushforwardStalkFromRingLinearMap f (f x) r)) =
        f.stalkMap x r := by
  intro r
  obtain ⟨U, hxU, a, rfl⟩ := Y.presheaf.exists_germ_eq r
  let uY := presheafOfModules_unitStalkLinearEquiv Y.presheaf (f x)
  apply (presheafOfModules_unitStalkLinearEquiv X.presheaf x).injective
  rw [(presheafOfModules_unitStalkLinearEquiv X.presheaf x).apply_symm_apply]
  have huY := presheafOfModules_unitStalkAddEquiv_germ
    Y.presheaf (f x) U hxU a
  change uY (Y.presheaf.germ U (f x) hxU a) = _ at huY
  dsimp [closedImmersionPushforwardStalkFromRingLinearMap,
    LinearMap.comp_apply]
  rw [huY]
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (C := AddCommGrpCat)
    (F := (PresheafOfModules.toPresheaf
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).obj
        (SheafOfModules.unit Y.ringCatSheaf).val)
    (G := (PresheafOfModules.toPresheaf
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).obj
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val)
    (f := (PresheafOfModules.toPresheaf
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f).val)
    U (f x) hxU a
  have hmap' :
      (schemeModuleStalkLinearMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) (f x))
          (TopCat.Presheaf.germ
            (PresheafOfModules.unit
              (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf
            U (f x) hxU a) =
        TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).presheaf
          U (f x) hxU
          ((IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f).val.app
            (Opposite.op U) a) := by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat (f x)).map
      ((PresheafOfModules.toPresheaf
        (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f).val)
        (TopCat.Presheaf.germ
          (PresheafOfModules.unit
            (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).presheaf
          U (f x) hxU a) = _
    convert hmap using 1 <;> rfl
  erw [hmap']
  have happ := SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    f.toRingCatSheafHom (X := Opposite.op U) a
  change
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f).val.app
        (Opposite.op U) a = f.app U a at happ
  rw [happ]
  have hpush :
      TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
        (TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).presheaf
          U (f x) hxU (f.app U a)) =
        TopCat.Presheaf.germ
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          (f ⁻¹ᵁ U) x hxU (f.app U a) := by
    have h := TopCat.Presheaf.stalkPushforward_germ_apply
      AddCommGrpCat f.base
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf
      U x hxU (f.app U a)
    convert h using 1 <;> rfl
  erw [hpush]
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact (presheafOfModules_unitStalkAddEquiv_germ
    X.presheaf x (f ⁻¹ᵁ U) hxU (f.app U a)).symm



set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For an inducing map, the pushed-forward unit-module stalk element attached
to a local-ring element vanishes exactly when the scheme stalk map does. -/
theorem closedImmersionPushforwardStalkFromRingLinearMap_eq_zero_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base)
    (x : X) (r : Y.presheaf.stalk (f x)) :
    closedImmersionPushforwardStalkFromRingLinearMap f (f x) r = 0 ↔
      f.stalkMap x r = 0 := by
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base
    (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
  haveI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat hf
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
  let uX := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  have h :=
    closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward f x r
  constructor
  · intro hz
    rw [hz, map_zero, map_zero] at h
    exact h.symm
  · intro hz
    have hcomp : uX.symm (push
        (closedImmersionPushforwardStalkFromRingLinearMap f (f x) r)) = 0 :=
      h.trans hz
    have hpush : push
        (closedImmersionPushforwardStalkFromRingLinearMap f (f x) r) = 0 := by
      apply uX.symm.injective
      simpa using hcomp
    apply (ConcreteCategory.bijective_of_isIso push).injective
    exact hpush.trans (map_zero (ConcreteCategory.hom push)).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The zero-kernel comparison in terms of the literal stalk map of the
module-sheaf morphism `O_Y -> f_* O_X`. -/
theorem closedImmersionUnitToPushforwardUnit_stalkMap_eq_zero_iff
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsInducing f.base)
    (x : X) (r : Y.presheaf.stalk (f x)) :
    (schemeModuleStalkLinearMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) (f x))
      ((presheafOfModules_unitStalkLinearEquiv Y.presheaf (f x)) r) = 0 ↔
      f.stalkMap x r = 0 := by
  change closedImmersionPushforwardStalkFromRingLinearMap f (f x) r = 0 ↔ _
  exact closedImmersionPushforwardStalkFromRingLinearMap_eq_zero_iff f hf x r


set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms of scheme modules are equal if their maps on every literal
stalk agree. -/
theorem schemeModule_hom_ext_of_stalkMap_eq
    {X : Scheme.{u}} {M N : X.Modules} (f g : M ⟶ N)
    (h : ∀ x : X, (schemeModuleStalkFunctor X x).map f =
      (schemeModuleStalkFunctor X x).map g) : f = g := by
  apply Scheme.Modules.hom_ext f g
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj N) U
      (f.app U s) (g.app U s)
  intro x hx
  change N.presheaf.germ U x hx (f.app U s) =
    N.presheaf.germ U x hx (g.app U s)
  have hfGerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    U x hx f.mapPresheaf s
  have hgGerm := TopCat.Presheaf.stalkFunctor_map_germ_apply
    U x hx g.mapPresheaf s
  simp only [Scheme.Modules.mapPresheaf_app] at hfGerm hgGerm
  rw [← hfGerm, ← hgGerm]
  exact DFunLike.congr_fun (congr_arg ConcreteCategory.hom (h x)) _

namespace ProjectiveNegativeTwist

open scoped DirectSum Pointwise
open DirectSum SetLike Localization Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication into the structure sheaf, followed by the canonical
identification `O -> O(0)`, is the original multiplication map into `O(0)`. -/
theorem mulHomogeneousToUnit_comp_unitToZeroTwist {d : ℕ} (s : 𝒜 d) :
    mulHomogeneousToUnit 𝒜 s ≫ unitToZeroTwist 𝒜 =
      mulHomogeneous 𝒜 s 0 := by
  letI : IsIso (unitToZeroTwist 𝒜) := unitToZeroTwist_isIso 𝒜
  let e := asIso (unitToZeroTwist 𝒜)
  change (mulHomogeneous 𝒜 s 0 ≫ e.inv) ≫ e.hom = _
  rw [Category.assoc, e.inv_hom_id, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Under the Proj local-ring identification, the actual categorical stalk
map `O(-d) -> O` is multiplication by the homogeneous equation on the
concrete homogeneous-fraction stalk. -/
theorem mulHomogeneousToUnit_stalkMap_compat {d : ℕ} (s : 𝒜 d)
    (x : Proj 𝒜)
    (z : (sheafOfModules 𝒜 (0 + d)).presheaf.stalk x) :
    Proj.stalkIso' 𝒜 x
        ((presheafOfModules_unitStalkLinearEquiv
          (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x).symm
          ((schemeModuleStalkFunctor (Proj 𝒜) x).map
            (mulHomogeneousToUnit 𝒜 s) z)) =
      (atPrimeLinearEquivZeroTwistStalk 𝒜
        (pointIdeal 𝒜 x)).symm
        (mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s 0
          (stalkToFractionModule 𝒜 (0 + d) x z)) := by
  let u := presheafOfModules_unitStalkLinearEquiv
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x
  let p := Proj.stalkIso' 𝒜 x
  let e := atPrimeLinearEquivZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
  let t := stalkToFractionModule 𝒜 0 x
  let g := (schemeModuleStalkFunctor (Proj 𝒜) x).map
    (mulHomogeneousToUnit 𝒜 s)
  let h := (schemeModuleStalkFunctor (Proj 𝒜) x).map
    (unitToZeroTwist 𝒜)
  let m := (schemeModuleStalkFunctor (Proj 𝒜) x).map
    (mulHomogeneous 𝒜 s 0)
  have hcomp := mulHomogeneousToUnit_comp_unitToZeroTwist s
  have hmaps := congrArg
    (fun q => (schemeModuleStalkFunctor (Proj 𝒜) x).map q) hcomp
  rw [Functor.map_comp] at hmaps
  have hpoint : h (g z) = m z := by
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom hmaps) z
  have hu := unitToZeroTwist_stalkMap_compat 𝒜 x (u.symm (g z))
  change t (h (u (u.symm (g z)))) = e (p (u.symm (g z))) at hu
  rw [u.apply_symm_apply] at hu
  apply e.injective
  rw [e.apply_symm_apply]
  calc
    e (p (u.symm (g z))) = t (h (g z)) := hu.symm
    _ = t (m z) := congr_arg t hpoint
    _ = mulHomogeneousStalk 𝒜 (pointIdeal 𝒜 x) s 0
        (stalkToFractionModule 𝒜 (0 + d) x z) := by
      exact stalkToFractionModule_stalkMap 𝒜 s 0 x z



/-- For the standard polynomial grading with a small variable type, the
degree-one homogeneous elements generate the irrelevant ideal. -/
theorem mvPolynomial_irrelevant_le_span_degreeOne_small :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 =>
        (f : MvPolynomial σ K))) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hpvars : p ∈ MvPolynomial.idealOfVars σ K := by
    rw [← pow_one (MvPolynomial.idealOfVars σ K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro mon hmon
    have he : mon.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hmon).symm
    exact he ▸ hn
  have hle : MvPolynomial.idealOfVars σ K ≤
      Ideal.span (Set.range (fun f : 𝒜 1 =>
        (f : MvPolynomial σ K))) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩, rfl⟩
  exact hle hpvars

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Away from the vanishing locus of a homogeneous polynomial, the actual
stalk map `O(-d) -> O` is an isomorphism. -/
theorem mulHomogeneousToUnit_stalkMap_isIso_of_not_mem
    {d : ℕ} (s : 𝒜 d) (x : Proj 𝒜)
    (hs : (s : MvPolynomial σ K) ∉ x.asHomogeneousIdeal.toIdeal)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 =>
        (f : MvPolynomial σ K)))) :
    IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
      (mulHomogeneousToUnit 𝒜 s)) := by
  let F := schemeModuleStalkFunctor (Proj 𝒜) x
  let a := F.map (mulHomogeneousToUnit 𝒜 s)
  let b := F.map (unitToZeroTwist 𝒜)
  haveI : IsIso b := unitToZeroTwist_stalkMap_isIso 𝒜 x
  rw [← isIso_comp_right_iff a b]
  rw [← F.map_comp, mulHomogeneousToUnit_comp_unitToZeroTwist]
  change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
    (mulHomogeneousPresheaf 𝒜 s 0))
  letI : (pointIdeal 𝒜 x).IsPrime := ProjectiveSpectrum.isPrime x
  have hs' : (s : MvPolynomial σ K) ∈
      (pointIdeal 𝒜 x).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    exact hs
  exact mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
    𝒜 s 0 x hs' hspan

/-- The image in ambient projective space of a point on the hypersurface.
Naming this point keeps later stalk statements compact enough to elaborate at
ordinary heartbeat limits. -/
noncomputable def hypersurfaceAmbientPoint
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (y : hypersurface p hp) : Proj 𝒜 :=
  hypersurfaceToAmbient p hp y

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- At every point of a projective hypersurface with domain coordinate ring,
the actual module-sheaf stalk sequence `O(-d) -> O -> i_* O_S` is exact. -/
theorem hypersurface_stalk_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (y : hypersurface p hp) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩)
        (hypersurfaceAmbientPoint p hp y))
      (schemeModuleStalkLinearMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (hypersurfaceToAmbient p hp))
        (hypersurfaceAmbientPoint p hp y)) := by
  let I := equationIdeal p hp
  let ℬ := grading I
  let q := quotientGradedRingHom I
  let i := quotientProjMap I
  let x := ProjectiveSpectrum.comap q
    (irrelevant_le_map_quotientGradedRingHom I) y
  let uA := presheafOfModules_unitStalkLinearEquiv
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x
  let P := Proj.stalkIso' 𝒜 x
  let Q := Proj.stalkIso' ℬ y
  let t := stalkAddEquivFractionModule 𝒜 (0 + d) x
  let F := fun z : stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal (0 + d) =>
    (atPrimeLinearEquivZeroTwistStalk 𝒜 x.asHomogeneousIdeal.toIdeal).symm
      (mulHomogeneousStalk 𝒜 x.asHomogeneousIdeal.toIdeal ⟨p, hp⟩ 0 z)
  let G := HomogeneousLocalization.localRingHom q
    x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal rfl
  let fA := schemeModuleStalkLinearMap
    (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩) x
  let gA := schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
  have hlocal : Function.Exact F G := by
    exact hypersurface_localRing_exact p hp y
  change Function.Exact fA gA
  intro v
  obtain ⟨r, rfl⟩ := uA.surjective v
  have hq : gA (uA r) = 0 ↔ i.stalkMap y r = 0 := by
    exact closedImmersionUnitToPushforwardUnit_stalkMap_eq_zero_iff
      i i.isClosedEmbedding.isInducing y r
  have hproj : Q.symm (G (P r)) = i.stalkMap y r := by
    exact Proj.localRingHom_comp_stalkIso_apply q
      (irrelevant_le_map_quotientGradedRingHom I) y r
  constructor
  · intro hg
    have hstalk : i.stalkMap y r = 0 := hq.mp hg
    have hG : G (P r) = 0 := by
      apply Q.symm.injective
      rw [map_zero, hproj, hstalk]
    obtain ⟨w, hw⟩ := (hlocal (P r)).mp hG
    obtain ⟨z, rfl⟩ := t.surjective w
    refine ⟨z, ?_⟩
    apply uA.symm.injective
    apply P.injective
    rw [uA.symm_apply_apply]
    calc
      P (uA.symm (fA z)) = F (t z) :=
        mulHomogeneousToUnit_stalkMap_compat ⟨p, hp⟩ x z
      _ = P r := hw
  · rintro ⟨z, hz⟩
    have hrange : P r ∈ Set.range F := by
      refine ⟨t z, ?_⟩
      calc
        F (t z) = P (uA.symm (fA z)) :=
          (mulHomogeneousToUnit_stalkMap_compat ⟨p, hp⟩ x z).symm
        _ = P r := by rw [hz, uA.symm_apply_apply]
    have hG : G (P r) = 0 := (hlocal (P r)).mpr hrange
    have hstalk : i.stalkMap y r = 0 := by
      rw [← hproj, hG, map_zero]
    exact hq.mpr hstalk


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual module-sheaf stalk sequence `O(-d) -> O -> i_* O_S` is exact
at every ambient projective point. On the hypersurface this is the local-ring
calculation above; off it, multiplication by the equation is an isomorphism
and the pushforward stalk is zero. -/
theorem hypersurface_stalk_exact_all
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    (x : Proj 𝒜) :
    Function.Exact
      (schemeModuleStalkLinearMap
        (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩) x)
      (schemeModuleStalkLinearMap
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (hypersurfaceToAmbient p hp)) x) := by
  let i := hypersurfaceToAmbient p hp
  let fA := schemeModuleStalkLinearMap
    (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩) x
  let gA := schemeModuleStalkLinearMap
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) x
  change Function.Exact fA gA
  by_cases hx : x ∈ Set.range i
  · obtain ⟨y, rfl⟩ := hx
    exact hypersurface_stalk_exact p hp y
  · have hpnot : p ∉ x.asHomogeneousIdeal.toIdeal := by
      intro hpx
      apply hx
      change x ∈ Set.range
        (quotientProjMap (equationIdeal p hp))
      rw [quotientProjMap_mem_range_iff]
      change Ideal.span ({p} : Set (MvPolynomial σ K)) ≤
        x.asHomogeneousIdeal.toIdeal
      rw [Ideal.span_le]
      simpa only [Set.singleton_subset_iff]
    have hIso :=
      mulHomogeneousToUnit_stalkMap_isIso_of_not_mem ⟨p, hp⟩ x hpnot
        mvPolynomial_irrelevant_le_span_degreeOne_small
    letI : IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩)) := hIso
    have hsurj := (ConcreteCategory.bijective_of_isIso
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩))).surjective
    change Function.Surjective fA at hsurj
    let _ : Subsingleton
        (((Scheme.Modules.pushforward i).obj
          (SheafOfModules.unit (hypersurface p hp).ringCatSheaf)).presheaf.stalk x) :=
      schemeModulePushforward_stalk_subsingleton_off_range i
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) x hx
    intro v
    constructor
    · intro _
      exact hsurj v
    · intro _
      exact Subsingleton.elim _ _


set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Multiplication by the defining equation maps to zero in the pushed-forward
structure sheaf of the hypersurface. -/
theorem mulHomogeneousToUnit_comp_hypersurfaceUnitToPushforward_eq_zero
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    mulHomogeneousToUnit 𝒜 ⟨p, hp⟩ ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (hypersurfaceToAmbient p hp) = 0 := by
  apply schemeModule_hom_ext_of_stalkMap_eq
  intro x
  let F := schemeModuleStalkFunctor (Proj 𝒜) x
  letI : F.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive F
  change F.map (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩ ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (hypersurfaceToAmbient p hp)) = F.map 0
  rw [F.map_comp, F.map_zero]
  apply ConcreteCategory.hom_ext
  intro z
  change (schemeModuleStalkLinearMap
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (hypersurfaceToAmbient p hp)) x)
      ((schemeModuleStalkLinearMap
        (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩) x) z) = 0
  have h := hypersurface_stalk_exact_all p hp x
  exact (h _).mpr ⟨z, rfl⟩


/-- The untwisted projective hypersurface restriction sequence with its
actual pushed-forward structure sheaf as the third term. -/
noncomputable def hypersurfaceRestrictionSequence
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.mk
    (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩)
    (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (hypersurfaceToAmbient p hp))
    (mulHomogeneousToUnit_comp_hypersurfaceUnitToPushforward_eq_zero p hp)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual untwisted hypersurface restriction sequence is exact. -/
theorem hypersurfaceRestrictionSequence_exact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    (hypersurfaceRestrictionSequence p hp).Exact := by
  let S := hypersurfaceRestrictionSequence p hp
  let T := SheafOfModules.toSheaf.{u} (Proj 𝒜).ringCatSheaf
  letI : T.PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive T
  apply Functor.reflects_exact_of_faithful T
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact (S.map T)).mpr
  intro x
  change (S.map (schemeModuleStalkFunctor (Proj 𝒜) x)).Exact
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (hypersurface_stalk_exact_all p hp x)

/-- For a nonzero equation, the actual untwisted hypersurface restriction
sequence is short exact. -/
theorem hypersurfaceRestrictionSequence_shortExact
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    (hypersurfaceRestrictionSequence p hp).ShortExact := by
  let S := hypersurfaceRestrictionSequence p hp
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · exact hypersurfaceRestrictionSequence_exact p hp
  · change Mono (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩)
    exact mulHomogeneousToUnit_mono 𝒜 ⟨p, hp⟩ hp0
  · change Epi (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (hypersurfaceToAmbient p hp))
    infer_instance

/-- The cokernel of multiplication by a nonzero homogeneous equation is the
pushed-forward structure sheaf of the corresponding projective hypersurface. -/
noncomputable def hypersurfaceCokernelIsoPushforward
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))] :
    cokernel (mulHomogeneousToUnit 𝒜 ⟨p, hp⟩) ≅
      (Scheme.Modules.pushforward (hypersurfaceToAmbient p hp)).obj
        (SheafOfModules.unit (hypersurface p hp).ringCatSheaf) := by
  let S := hypersurfaceRestrictionSequence p hp
  have hS : S.ShortExact :=
    hypersurfaceRestrictionSequence_shortExact p hp hp0
  exact IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel S.f) hS.gIsCokernel

end ProjectiveNegativeTwist

end PfaffianDescent
