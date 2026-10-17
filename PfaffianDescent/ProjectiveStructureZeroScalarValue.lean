import PfaffianDescent.VoisinPositiveTwistTriviality
import PfaffianDescent.SchemeAffineFunctions

noncomputable section
namespace PfaffianDescent.ProjectiveStructureNative
open CategoryTheory AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
universe u
variable {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
  (G : ℕ → ρ) [GradedRing G]

lemma projectiveStructureZero_section
    (b : G 0) :
    affineFunctionHom (Proj.toSpecZero G) b =
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1)) ≫
        Proj.awayToSection G 1 ≫
        (Proj.basicOpen G 1).topIso.inv ≫
        ((Proj G).isoOfEq (Proj.basicOpen_one G)).inv.appTop ≫
        (Proj G).topIso.inv.appTop).hom b) := by
  unfold affineFunctionHom
  rw [Proj.toSpecZero]
  simp only [Scheme.Hom.comp_appTop, Category.assoc]
  simp only [Proj.basicOpenToSpec, Scheme.Hom.comp_appTop,
    Scheme.Opens.toSpecΓ_appTop, Category.assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc]
  rw [← Scheme.ΓSpecIso_inv_naturality_assoc
    (Proj.awayToSection G 1)]
  simp

private lemma open_eq_top_section_transport_apply
    (U : (Proj G).Opens) (e : U = ⊤) (s : Γ(Proj G, U))
    (x : ProjectiveSpectrum.top G) :
    (((U.topIso.inv ≫ ((Proj G).isoOfEq e).inv.appTop ≫
      (Proj G).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) =
        s.1 ⟨x, e.symm ▸ trivial⟩ := by
  subst U
  simp only [Scheme.isoOfEq_rfl, Iso.refl_inv]
  change ((((Proj G).topIso.hom.appTop ≫
    (Proj G).topIso.inv.appTop).hom s).1 ⟨x, trivial⟩) = _
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


/-- Literal original structure-map value at every original projective point. -/
lemma projectiveStructureZero_value (b : G 0) (x : ProjectiveSpectrum.top G) :
    ((affineFunctionHom (Proj.toSpecZero G) b).1 ⟨x, trivial⟩).val =
      Localization.mk (b : A) (1 : (pointIdeal G x).primeCompl) := by
  rw [projectiveStructureZero_section G]
  let U := Proj.basicOpen G 1
  let e : U = (⊤ : (Proj G).Opens) := Proj.basicOpen_one G
  let s : Γ(Proj G, U) :=
    (Proj.awayToSection G 1).hom
      (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1) b)
  have htransport := open_eq_top_section_transport_apply G U e s x
  have hsection :
      ((CommRingCat.ofHom
          (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1)) ≫
        Proj.awayToSection G 1 ≫ U.topIso.inv ≫
        ((Proj G).isoOfEq e).inv.appTop ≫
        (Proj G).topIso.inv.appTop).hom b) =
      ((U.topIso.inv ≫ ((Proj G).isoOfEq e).inv.appTop ≫
        (Proj G).topIso.inv.appTop).hom s) := rfl
  rw [hsection, htransport]
  dsimp only [s]
  let y : U := ⟨x, e.symm ▸ trivial⟩
  have haw := ProjectiveSpectrum.Proj.awayToSection_apply G
    (1 : A)
    (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1)
      b) y
  change HomogeneousLocalization.val
    (((CommRingCat.Hom.hom (Proj.awayToSection G 1))
      (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1)
        b)).1 y) = _ at haw
  have hbval :
      (HomogeneousLocalization.fromZeroRingHom G (Submonoid.powers 1)
        b).val =
      Localization.mk (b : A)
        (1 : Submonoid.powers (1 : A)) := rfl
  rw [hbval] at haw
  have hMN : Submonoid.powers (1 : A) ≤
      Submonoid.comap (RingHom.id (A))
        (pointIdeal G x).primeCompl := by
    intro z hz
    exact (Submonoid.powers_le.mpr y.2) hz
  have hmap := localizationMap_mk_one
    (Submonoid.powers (1 : A))
    (pointIdeal G x).primeCompl hMN
    (b : A)
  rw [hmap] at haw
  have hbcoord : (b :
      A) = (b : A) := rfl
  have haw' := haw.trans (congrArg
    (fun z => Localization.mk z (1 : (pointIdeal G x).primeCompl)) hbcoord)
  convert haw' using 1 <;> rfl

end PfaffianDescent.ProjectiveStructureNative
end
