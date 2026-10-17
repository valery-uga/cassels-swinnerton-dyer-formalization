import PfaffianDescent.SchemeAffineFunctions
import AllCharacteristics.HomogeneousProjectiveAmbient
import PfaffianDescent.PlaneNativeCechCover
/-! SOURCE ONLY / UNCHECKED. Literal actual ambient P2 structure map
and its coefficient pullback values, without defining a scalar action by
transport or assuming global-function normalization. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
/-- The standard projective-space structure map to the ground field. -/
noncomputable def p2BaseMap : Proj PS ⟶ Spec (.of K) :=
  Proj.toSpecZero PS ≫
    Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))

private lemma affineFunctionHom_toSpecZero_section
    (b : PS 0) :
    affineFunctionHom (Proj.toSpecZero PS) b =
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)) ≫
        Proj.awayToSection PS 1 ≫
        (Proj.basicOpen PS 1).topIso.inv ≫
        ((Proj PS).isoOfEq (Proj.basicOpen_one PS)).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom b) := by
  unfold affineFunctionHom
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  simp only [Proj.basicOpenToSpec, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc
    (Proj.awayToSection PS 1)]
  simp

private lemma open_eq_top_section_transport_apply
    (U : (Proj PS).Opens) (e : U = ⊤) (s : Γ(Proj PS, U))
    (x : ProjectiveSpectrum.top PS) :
    (((U.topIso.inv ≫ ((Proj PS).isoOfEq e).inv.appTop ≫
      (Proj PS).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) =
        s.1 ⟨x, e.symm ▸ trivial⟩ := by
  subst U
  simp only [Scheme.isoOfEq_rfl, Iso.refl_inv]
  change ((((Proj PS).topIso.hom.appTop ≫
    (Proj PS).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) = _
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  rfl

private lemma localizationMap_mk_one
    {R : Type u} [CommRing R] (M N : Submonoid R)
    (h : M ≤ Submonoid.comap (RingHom.id R) N) (r : R) :
    IsLocalization.map (Localization N) (RingHom.id R)
        h (Localization.mk r (1 : M)) =
      Localization.mk r (1 : N) := by
  rw [Localization.mk_eq_mk', IsLocalization.map_mk']
  rw [← Localization.mk_eq_mk']
  congr 2

set_option backward.isDefEq.respectTransparency false

/-- The actual structure morphism sends a ground-field scalar to the same
fraction `C c / 1` at every projective point. -/
theorem p2BaseMap_scalar_value
    (c : K) (x : ProjectiveSpectrum.top PS) :
    ((affineFunctionHom (p2BaseMap K) c).1 ⟨x, trivial⟩).val =
      Localization.mk (MvPolynomial.C c : MvPolynomial (Fin 3) K)
        (1 : (pointIdeal PS x).primeCompl) := by
  change ((affineFunctionHom
      (Proj.toSpecZero PS ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))) c).1
        ⟨x, trivial⟩).val = _
  have hbase : affineFunctionHom
      (Proj.toSpecZero PS ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (PS 0)))) c =
      affineFunctionHom (Proj.toSpecZero PS)
        (algebraMap K (PS 0) c) := by
    simpa using congrArg (fun f => f c)
      (affineFunctionHom_comp_Spec (Proj.toSpecZero PS)
        (algebraMap K (PS 0)))
  rw [hbase]
  rw [affineFunctionHom_toSpecZero_section K]
  let U := Proj.basicOpen PS 1
  let e : U = (⊤ : (Proj PS).Opens) := Proj.basicOpen_one PS
  let b : PS 0 := algebraMap K (PS 0) c
  let s : Γ(Proj PS, U) :=
    (Proj.awayToSection PS 1).hom
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1) b)
  have htransport := open_eq_top_section_transport_apply K U e s x
  have hsection :
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)) ≫
        Proj.awayToSection PS 1 ≫ U.topIso.inv ≫
        ((Proj PS).isoOfEq e).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom b) =
      ((U.topIso.inv ≫ ((Proj PS).isoOfEq e).inv.appTop ≫
        (Proj PS).topIso.inv.appTop).hom s) := rfl
  rw [hsection, htransport]
  dsimp only [s, b]
  let y : U := ⟨x, e.symm ▸ trivial⟩
  have haw := ProjectiveSpectrum.Proj.awayToSection_apply PS
    (1 : MvPolynomial (Fin 3) K)
    (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
      (algebraMap K (PS 0) c)) y
  change HomogeneousLocalization.val
    (((CommRingCat.Hom.hom (Proj.awayToSection PS 1))
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
        (algebraMap K (PS 0) c))).1 y) = _ at haw
  have hbval :
      (HomogeneousLocalization.fromZeroRingHom PS (Submonoid.powers 1)
        (algebraMap K (PS 0) c)).val =
      Localization.mk ((algebraMap K (PS 0) c) : MvPolynomial (Fin 3) K)
        (1 : Submonoid.powers (1 : MvPolynomial (Fin 3) K)) := rfl
  rw [hbval] at haw
  have hMN : Submonoid.powers (1 : MvPolynomial (Fin 3) K) ≤
      Submonoid.comap (RingHom.id (MvPolynomial (Fin 3) K))
        (pointIdeal PS x).primeCompl := by
    intro z hz
    exact (Submonoid.powers_le.mpr y.2) hz
  have hmap := localizationMap_mk_one
    (Submonoid.powers (1 : MvPolynomial (Fin 3) K))
    (pointIdeal PS x).primeCompl hMN
    ((algebraMap K (PS 0) c) : MvPolynomial (Fin 3) K)
  rw [hmap] at haw
  have hbcoord : ((algebraMap K (PS 0) c) :
      MvPolynomial (Fin 3) K) = MvPolynomial.C c := rfl
  have haw' := haw.trans (congrArg
    (fun z => Localization.mk z (1 : (pointIdeal PS x).primeCompl)) hbcoord)
  simpa only [y, b] using haw'


end PfaffianDescent.ProjectivePlaneNative
