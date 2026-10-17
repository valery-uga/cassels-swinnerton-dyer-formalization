import PfaffianDescent.CorayActualPositiveNativeWholeGeneratorMatrix
import PfaffianDescent.CorayActualAmbientIdealPositiveNativeChart
import PfaffianDescent.OpenPullbackMono
import PfaffianDescent.AffineQCAcyclicity
import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-! Monicity of the literal whole homogeneous ideal tensor O(m) inclusion.
The actual chart comparison and original four-coordinate cover derive the
result. No monicity, image identification, or Serre certificate is supplied.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma mono_of_isoSquare
    {C : Type*} [Category C] {M M' N N' : C}
    (e : M ≅ M') (u : N ≅ N') (a : M ⟶ N) (b : M' ⟶ N') [Mono b]
    (h : e.hom ≫ b = a ≫ u.hom) : Mono a := by
  have ha : a = (e.hom ≫ b) ≫ u.inv := by
    calc
      a = (a ≫ u.hom) ≫ u.inv := by simp only [Category.assoc,
        u.hom_inv_id, Category.comp_id]
      _ = (e.hom ≫ b) ≫ u.inv := congrArg (fun z => z ≫ u.inv) h.symm
  rw [ha]
  infer_instance

private theorem isoPullback_faithful
    {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.inv).Faithful := by
  let P := Scheme.Modules.pullback e.inv
  let Q := Scheme.Modules.pullback e.hom
  let E : P ⋙ Q ≅ 𝟭 X.Modules :=
    Scheme.Modules.pullbackComp e.hom e.inv ≪≫
      Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X
  exact CategoryTheory.Functor.Faithful.of_comp_iso E

/-- On the SAME native away chart, the literal ideal-twist inclusion is
monic because its actual chart frame identifies it with tilde of the OWN
quotient-kernel subtype. All nilpotents in the whole ideal are retained. -/
theorem actualAmbientIdealPositiveInclusion_nativeChart_mono
    (I : HomogeneousIdeal PS) (j : Fin 4) (m : ℕ) :
    Mono ((Scheme.Modules.pullback
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).map
      (actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m))) := by
  let B := HomogeneousLocalization.Away PS (X j)
  let R := CommRingCat.of B
  let F := tilde.functor R
  let Q := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let v := actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)
  let k := ModuleCat.ofHom (RingHom.ker (quotientAmbientChartMap I j)).subtype
  let t := tildeSelf (R := R)
  let J := actualAmbientHomogeneousIdealPositiveNativeChartIso I j m
  let em := actualAmbientPositiveNativeChartUnitIso (K := K) j m
  letI : Mono k := (ModuleCat.mono_iff_injective k).mpr Subtype.val_injective
  letI : F.PreservesMonomorphisms := PfaffianDescent.tilde_preservesMonomorphisms (R := R)
  let N : (Spec R).Modules := F.obj (ModuleCat.of B (RingHom.ker (quotientAmbientChartMap I j)))
  let O : (Spec R).Modules := SheafOfModules.unit (Spec R).ringCatSheaf
  let w : N ⟶ O := F.map k ≫ t.hom
  letI : Mono (F.map k) := Functor.map_mono F k
  letI : Mono w := by
    dsimp only [w]
    infer_instance
  have hi : J.hom ≫ w = Q.map v ≫ em.hom :=
    actualAmbientHomogeneousIdealPositiveNativeChartIso_inclusion I j m
  exact mono_of_isoSquare (C := (Spec R).Modules) J em (Q.map v) w hi

/-- Globally, the SAME original ideal tensor O(m) inclusion is monic.
The four native coordinate charts cover the original Proj; actual restriction
and stalk comparisons transport the internally proved local monicity. -/
theorem actualAmbientIdealPositiveInclusion_mono
    (I : HomogeneousIdeal PS) (m : ℕ) :
    Mono (actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)) := by
  let v := actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)
  apply schemeModule_mono_of_stalk_mono v
  intro x
  have hx : x ∈ (⨆ j : Fin 4, p3StandardOpen (K := K) j) := by
    rw [p3StandardOpen_iSup K]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let U := p3StandardOpen (K := K) j
  let y : U.toScheme := ⟨x, hj⟩
  let e := Proj.basicOpenIsoSpec PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1)
  let P := Scheme.Modules.pullback e.inv
  let R := Scheme.Modules.restrictFunctor U.ι
  letI : P.Faithful := isoPullback_faithful e
  have hlocal : Mono ((R ⋙ P).map v) :=
    mono_map_of_natIso (actualPositiveNativeChartRestrictionIso (K := K) j) v
      (actualAmbientIdealPositiveInclusion_nativeChart_mono I j m)
  have hrestrict : Mono (R.map v) :=
    (CategoryTheory.Functor.reflectsMonomorphisms_of_faithful P).reflects (R.map v) hlocal
  letI : Mono (R.map v) := hrestrict
  have hstalk : Mono ((schemeModuleStalkFunctor U.toScheme y).map (R.map v)) :=
    schemeModuleStalkFunctor_map_mono (R.map v) y
  exact mono_map_of_natIso (Scheme.Modules.restrictStalkNatIso U.ι y) v hstalk

end PfaffianDescent.Coray
