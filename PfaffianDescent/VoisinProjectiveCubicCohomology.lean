import PfaffianDescent.ProjectiveNegativeTwistStalk
import PfaffianDescent.VoisinL2Cohomology
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Voisin's negative-three cohomology sequence with concrete Proj twists

This file instantiates the abstract `l = 2` cohomology reduction with the
actual negative twisting sheaves and multiplication-by-a-cubic morphism
constructed in `ProjectiveNegativeTwistStalk.lean`.
-/

noncomputable section

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace ProjectiveNegativeTwist

variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
local notation "X" => ProjectiveSpectrum.top 𝒜

/-- On stalks, the canonical map from the structure sheaf to the concrete
zero twist is the ordinary inclusion of the degree-zero homogeneous
localization into the full localization. -/
theorem unitToZeroTwist_stalkMap_compat
    (x : X)
    (a : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.stalk x) :
    let u := presheafOfModules_unitStalkLinearEquiv
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x
    stalkToFractionModule 𝒜 0 x
        ((schemeModuleStalkFunctor (Proj 𝒜) x).map
          (unitToZeroTwist 𝒜) (u a)) =
      atPrimeToZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
        (Proj.stalkIso' 𝒜 x a) := by
  dsimp only
  obtain ⟨U, hxU, r, rfl⟩ :=
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.exists_germ_eq a
  have hu :
      (presheafOfModules_unitStalkLinearEquiv
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x)
          ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ
            U x hxU r) =
        TopCat.Presheaf.germ
          (PresheafOfModules.unit
            ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf ⋙
              forget₂ CommRingCat RingCat)).presheaf U x hxU r := by
    exact presheafOfModules_unitStalkAddEquiv_germ
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x U hxU r
  rw [hu]
  have hmap := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
    ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
      (unitToZeroTwist 𝒜)).hom r
  change
    (schemeModuleStalkFunctor (Proj 𝒜) x).map (unitToZeroTwist 𝒜)
        (TopCat.Presheaf.germ
          (PresheafOfModules.unit
            ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf ⋙
              forget₂ CommRingCat RingCat)).presheaf U x hxU r) =
      TopCat.Presheaf.germ (C := AddCommGrpCat)
        (modulePresheaf 𝒜 0).presheaf U x hxU
          ((unitToZeroTwist 𝒜).val.app (op U) r) at hmap
  rw [hmap]
  have hfrac := stalkToFractionModule_germ 𝒜 0 U x hxU
    ((unitToZeroTwist 𝒜).val.app (op U) r)
  have hproj := Proj.stalkIso'_germ 𝒜 U x hxU r
  calc
    _ = sectionValue 𝒜 0 (op U)
        ((unitToZeroTwist 𝒜).val.app (op U) r) ⟨x, hxU⟩ := hfrac
    _ = atPrimeToZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
        (r.1 ⟨x, hxU⟩) := Subtype.ext rfl
    _ = atPrimeToZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
        (Proj.stalkIso' 𝒜 x
          ((ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.germ
            U x hxU r)) := congr_arg _ hproj.symm

/-- The canonical map from the structure sheaf to the concrete zero twist is
bijective on every actual categorical stalk. -/
theorem unitToZeroTwist_stalkMap_bijective (x : X) :
    Function.Bijective
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map (unitToZeroTwist 𝒜)) := by
  let u := presheafOfModules_unitStalkLinearEquiv
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf x
  let p := Proj.stalkIso' 𝒜 x
  let h := atPrimeLinearEquivZeroTwistStalk 𝒜 (pointIdeal 𝒜 x)
  let t := stalkAddEquivFractionModule 𝒜 0 x
  let g := (schemeModuleStalkFunctor (Proj 𝒜) x).map (unitToZeroTwist 𝒜)
  have hcompat (a :
      (ProjectiveSpectrum.Proj.structureSheaf 𝒜).presheaf.stalk x) :
      t (g (u a)) = h (p a) := by
    exact unitToZeroTwist_stalkMap_compat 𝒜 x a
  constructor
  · intro z w hzw
    obtain ⟨a, rfl⟩ := u.surjective z
    obtain ⟨b, rfl⟩ := u.surjective w
    congr 1
    apply p.injective
    apply h.injective
    calc
      h (p a) = t (g (u a)) := (hcompat a).symm
      _ = t (g (u b)) := congr_arg t hzw
      _ = h (p b) := hcompat b
  · intro z
    obtain ⟨q, hq⟩ := h.surjective (t z)
    obtain ⟨a, ha⟩ := p.surjective q
    refine ⟨u a, t.injective ?_⟩
    calc
      t (g (u a)) = h (p a) := hcompat a
      _ = h q := congr_arg h ha
      _ = t z := hq

/-- Categorical stalk form of `unitToZeroTwist_stalkMap_bijective`. -/
theorem unitToZeroTwist_stalkMap_isIso (x : X) :
    IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
      (unitToZeroTwist 𝒜)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    (unitToZeroTwist_stalkMap_bijective 𝒜 x)

/-- The concretely constructed zero twist is canonically isomorphic to the
structure sheaf as a module sheaf on `Proj A`. -/
theorem unitToZeroTwist_isIso : IsIso (unitToZeroTwist 𝒜) := by
  have hsheaf : IsIso
      ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
        (unitToZeroTwist 𝒜)) := by
    apply (TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso _).mpr
    intro x
    change IsIso ((schemeModuleStalkFunctor (Proj 𝒜) x).map
      (unitToZeroTwist 𝒜))
    exact unitToZeroTwist_stalkMap_isIso 𝒜 x
  letI : IsIso
      ((SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf).map
        (unitToZeroTwist 𝒜)) := hsheaf
  exact isIso_of_reflects_iso (unitToZeroTwist 𝒜)
    (SheafOfModules.toSheaf (Proj 𝒜).ringCatSheaf)

/-- The canonical isomorphism from the structure sheaf to the concrete zero
twist. -/
noncomputable def unitIsoZeroTwist :
    SheafOfModules.unit (Proj 𝒜).ringCatSheaf ≅ sheafOfModules 𝒜 0 := by
  letI : IsIso (unitToZeroTwist 𝒜) := unitToZeroTwist_isIso 𝒜
  exact asIso (unitToZeroTwist 𝒜)

/-- Multiplication by a homogeneous section, with the target concrete zero
twist identified with the structure sheaf. -/
def mulHomogeneousToUnit {d : ℕ} (s : 𝒜 d) :
    sheafOfModules 𝒜 (0 + d) ⟶
      SheafOfModules.unit (Proj 𝒜).ringCatSheaf :=
  mulHomogeneous 𝒜 s 0 ≫ (unitIsoZeroTwist 𝒜).inv

/-- Multiplication into the structure sheaf is a monomorphism over a domain
when the homogeneous section is nonzero. -/
theorem mulHomogeneousToUnit_mono [IsDomain A] {d : ℕ} (s : 𝒜 d)
    (hs : (s : A) ≠ 0) : Mono (mulHomogeneousToUnit 𝒜 s) := by
  let e := unitIsoZeroTwist 𝒜
  change Mono (mulHomogeneous 𝒜 s 0 ≫ e.inv)
  exact mono_comp' (mulHomogeneous_mono 𝒜 s hs 0)
    (@IsIso.mono_of_iso _ _ _ _ e.inv (Iso.isIso_inv e))

/-- The untwisted hypersurface restriction sequence ending in the canonical
cokernel of multiplication into the structure sheaf. -/
def zeroRestrictionSequence {d : ℕ} (s : 𝒜 d) :
    ShortComplex (Proj 𝒜).Modules :=
  ShortComplex.cokernelSequence (mulHomogeneousToUnit 𝒜 s)

/-- The untwisted hypersurface restriction sequence is short exact for a
nonzero equation over a domain. -/
theorem zeroRestrictionSequence_shortExact [IsDomain A]
    {d : ℕ} (s : 𝒜 d) (hs : (s : A) ≠ 0) :
    (zeroRestrictionSequence 𝒜 s).ShortExact := by
  let f := mulHomogeneousToUnit 𝒜 s
  let _ : Mono f := mulHomogeneousToUnit_mono 𝒜 s hs
  change (ShortComplex.mk f (cokernel.π f)
    (cokernel.condition f)).ShortExact
  exact { exact := ShortComplex.exact_cokernel f }

/-- Replacing the concrete zero twist by the structure sheaf does not change
the cokernel of multiplication. -/
noncomputable def zeroRestrictionCokernelIso {d : ℕ} (s : 𝒜 d) :
    cokernel (mulHomogeneousToUnit 𝒜 s) ≅
      cokernel (mulHomogeneous 𝒜 s 0) := by
  let e := unitIsoZeroTwist 𝒜
  change cokernel (mulHomogeneous 𝒜 s 0 ≫ e.inv) ≅
    cokernel (mulHomogeneous 𝒜 s 0)
  exact @cokernelCompIsIso _ _ _ _ _ _
    (mulHomogeneous 𝒜 s 0) e.inv inferInstance (Iso.isIso_inv e)

/-- The cokernel of multiplication by a homogeneous equation has zero stalk
away from its vanishing locus, provided degree one generates the irrelevant
ideal.  This is the actual categorical stalk of the sheaf cokernel, not only
the concrete fraction model. -/
theorem cokernel_stalk_isZero_of_not_mem
    {d : ℕ} (s : 𝒜 d) (m : ℕ) (x : Proj 𝒜)
    (hs : (s : A) ∉ x.asHomogeneousIdeal.toIdeal)
    (hspan : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤
      Ideal.span (Set.range (fun f : 𝒜 1 => (f : A)))) :
    IsZero ((schemeModuleStalkFunctor (Proj 𝒜) x).obj
      (cokernel (mulHomogeneous 𝒜 s m))) := by
  letI : (schemeModuleStalkFunctor (Proj 𝒜) x).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive
      (schemeModuleStalkFunctor (Proj 𝒜) x)
  haveI hIso : IsIso
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneous 𝒜 s m)) := by
    change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (mulHomogeneousPresheaf 𝒜 s m))
    letI : (pointIdeal 𝒜 x).IsPrime := ProjectiveSpectrum.isPrime x
    have hs' : (s : A) ∈ (pointIdeal 𝒜 x).primeCompl := by
      rw [Ideal.mem_primeCompl_iff]
      exact hs
    exact
      mulHomogeneous_stalkMap_isIso_of_mem_primeCompl_of_irrelevant_le_span
        𝒜 s m x hs' hspan
  have hzero : IsZero (cokernel
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneous 𝒜 s m))) :=
    isZero_cokernel_of_epi
      ((schemeModuleStalkFunctor (Proj 𝒜) x).map
        (mulHomogeneous 𝒜 s m))
  exact hzero.of_iso
    (PreservesCokernel.iso (schemeModuleStalkFunctor (Proj 𝒜) x)
      (mulHomogeneous 𝒜 s m))

/-- The cokernel of multiplication by a nonzero cubic has vanishing first
cohomology as soon as the two adjacent ambient projective cohomology groups
`H¹(O(-3))` and `H²(O(-6))` vanish. -/
theorem cubicCokernel_cohomology_one_subsingleton
    [IsDomain A] [HasExt.{u} (Proj 𝒜).Modules]
    (cubic : 𝒜 3) (hcubic : (cubic : A) ≠ 0)
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 3) 1)]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 6) 2)] :
    Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (cokernel (mulHomogeneous 𝒜 cubic 3)) 1) := by
  let R := homogeneousRestrictionSequence 𝒜 cubic 3
  have hR : R.ShortExact :=
    homogeneousRestrictionSequence_shortExact 𝒜 cubic hcubic 3
  exact schemeModuleCohomology_subsingleton_of_restriction_sequence_isos
    (Proj 𝒜) R hR 1
      (A := sheafOfModules 𝒜 6)
      (B := sheafOfModules 𝒜 3)
      (C := cokernel (mulHomogeneous 𝒜 cubic 3))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)

/-- Concrete `l = 2` cubic restriction endpoint.  Once the canonical
cokernel is identified with the pushforward of a surface module `M`, the two
ambient vanishings imply `H¹(S,M)=0`. -/
theorem cubicSurface_cohomology_one_subsingleton_of_cokernelIsoPushforward
    [IsDomain A] {S : Scheme.{u}}
    (cubic : 𝒜 3) (hcubic : (cubic : A) ≠ 0)
    (i : S ⟶ Proj 𝒜) [IsClosedImmersion i]
    [HasExt.{u} (Proj 𝒜).Modules] [HasExt.{u} S.Modules]
    [EnoughInjectives S.Modules]
    (M : S.Modules)
    (eRestriction : cokernel (mulHomogeneous 𝒜 cubic 3) ≅
      (Scheme.Modules.pushforward i).obj M)
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 3) 1)]
    [Subsingleton (schemeModuleCohomology (Proj 𝒜)
      (sheafOfModules 𝒜 6) 2)] :
    Subsingleton (schemeModuleCohomology S M 1) := by
  let R := homogeneousRestrictionSequence 𝒜 cubic 3
  have hR : R.ShortExact :=
    homogeneousRestrictionSequence_shortExact 𝒜 cubic hcubic 3
  exact
    schemeModuleCohomology_one_subsingleton_of_closedImmersion_restrictionSequence
      (A := sheafOfModules 𝒜 6)
      (B := sheafOfModules 𝒜 3)
      i M R hR (Iso.refl _) (Iso.refl _) eRestriction

end ProjectiveNegativeTwist

namespace ProjectiveNegativeTwist

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the standard grading on a polynomial ring, the degree-one
homogeneous elements generate the irrelevant ideal. -/
theorem mvPolynomial_irrelevant_le_span_degreeOne
    {K τ : Type u} [CommRing K] :
    (HomogeneousIdeal.irrelevant
      (MvPolynomial.homogeneousSubmodule τ K)).toIdeal ≤
      Ideal.span (Set.range (fun f :
        MvPolynomial.homogeneousSubmodule τ K 1 =>
          (f : MvPolynomial τ K))) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  have hpvars : p ∈ MvPolynomial.idealOfVars τ K := by
    rw [← pow_one (MvPolynomial.idealOfVars τ K),
      MvPolynomial.mem_pow_idealOfVars_iff]
    intro mon hmon
    have he : mon.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hmon).symm
    exact he ▸ hn
  have hle : MvPolynomial.idealOfVars τ K ≤
      Ideal.span (Set.range (fun f :
        MvPolynomial.homogeneousSubmodule τ K 1 =>
          (f : MvPolynomial τ K))) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    apply Ideal.subset_span
    exact ⟨⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X K i⟩, rfl⟩
  exact hle hpvars

/-- On projective space with its standard polynomial grading, the stalk of
the hypersurface cokernel is zero at every point where the defining equation
does not vanish. -/
theorem mvPolynomial_cokernel_stalk_isZero_of_not_mem
    {K τ : Type u} [CommRing K]
    {d : ℕ} (s : MvPolynomial.homogeneousSubmodule τ K d)
    (m : ℕ)
    (x : Proj (MvPolynomial.homogeneousSubmodule τ K))
    (hs : (s : MvPolynomial τ K) ∉ x.asHomogeneousIdeal.toIdeal) :
    IsZero ((schemeModuleStalkFunctor
      (Proj (MvPolynomial.homogeneousSubmodule τ K)) x).obj
      (cokernel (mulHomogeneous
        (MvPolynomial.homogeneousSubmodule τ K) s m))) :=
  cokernel_stalk_isZero_of_not_mem
    (MvPolynomial.homogeneousSubmodule τ K) s m x hs
      mvPolynomial_irrelevant_le_span_degreeOne

/-- Geometric support form of
`mvPolynomial_cokernel_stalk_isZero_of_not_mem`: the hypersurface cokernel
vanishes stalkwise on the complement of the projective zero locus of its
defining homogeneous polynomial. -/
theorem mvPolynomial_cokernel_stalk_isZero_off_zeroLocus
    {K τ : Type u} [CommRing K]
    {d : ℕ} (s : MvPolynomial.homogeneousSubmodule τ K d)
    (m : ℕ)
    (x : Proj (MvPolynomial.homogeneousSubmodule τ K))
    (hx : x ∉ ProjectiveSpectrum.zeroLocus
      (MvPolynomial.homogeneousSubmodule τ K)
      ({(s : MvPolynomial τ K)} : Set (MvPolynomial τ K))) :
    IsZero ((schemeModuleStalkFunctor
      (Proj (MvPolynomial.homogeneousSubmodule τ K)) x).obj
      (cokernel (mulHomogeneous
        (MvPolynomial.homogeneousSubmodule τ K) s m))) := by
  apply mvPolynomial_cokernel_stalk_isZero_of_not_mem s m x
  intro hs
  apply hx
  change ({(s : MvPolynomial τ K)} : Set (MvPolynomial τ K)) ⊆
    x.asHomogeneousIdeal
  rintro _ rfl
  change (s : MvPolynomial τ K) ∈ x.asHomogeneousIdeal.toIdeal
  exact hs

end ProjectiveNegativeTwist

end PfaffianDescent
