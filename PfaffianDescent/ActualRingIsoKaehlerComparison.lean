import Mathlib.Algebra.Category.ModuleCat.Differentials.Basic
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/- SOURCE ONLY / UNVERIFIED. Genuine differentials commute with an actual
ring Iso preserving the actual base map. The inverse is derived from the
inverse ring map, rather than assumed as a comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u
variable {k B C : CommRingCat.{u}}

/-- The canonical differential map along a base-compatible ring Iso is
an Iso after restriction of scalars, including its actual derivation. -/
def actualRingIsoKaehlerComparison
    (α : k ⟶ B) (α' : k ⟶ C) (e : B ≅ C) (h : α ≫ e.hom = α') :
    CommRingCat.KaehlerDifferential α ≅
      (ModuleCat.restrictScalars e.hom.hom).obj
        (CommRingCat.KaehlerDifferential α') := by
  have h' : α' ≫ e.inv = α := by rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]
  let a : CommRingCat.KaehlerDifferential α ⟶
      (ModuleCat.restrictScalars e.hom.hom).obj (CommRingCat.KaehlerDifferential α') :=
    CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.hom)
      (by simpa only [Category.id_comp] using h.symm)
  let b : CommRingCat.KaehlerDifferential α' ⟶
      (ModuleCat.restrictScalars e.inv.hom).obj (CommRingCat.KaehlerDifferential α) :=
    CommRingCat.KaehlerDifferential.map (g := 𝟙 k) (g' := e.inv)
      (by simpa only [Category.id_comp] using h'.symm)
  have hB : RingHom.id B = e.inv.hom.comp e.hom.hom := by
    exact (congrArg CommRingCat.Hom.hom e.hom_inv_id).symm
  have hC : RingHom.id C = e.hom.hom.comp e.inv.hom := by
    exact (congrArg CommRingCat.Hom.hom e.inv_hom_id).symm
  let cB := (ModuleCat.restrictScalarsComp'App e.hom.hom e.inv.hom
    (RingHom.id B) hB (CommRingCat.KaehlerDifferential α)).symm ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id B) rfl (CommRingCat.KaehlerDifferential α)
  let cC := (ModuleCat.restrictScalarsComp'App e.inv.hom e.hom.hom
    (RingHom.id C) hC (CommRingCat.KaehlerDifferential α')).symm ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id C) rfl (CommRingCat.KaehlerDifferential α')
  let back : (ModuleCat.restrictScalars e.hom.hom).obj
      (CommRingCat.KaehlerDifferential α') ⟶ CommRingCat.KaehlerDifferential α :=
    (ModuleCat.restrictScalars e.hom.hom).map b ≫ cB.hom
  have hleft : a ≫ back = 𝟙 _ := by
    apply CommRingCat.KaehlerDifferential.ext
    intro r
    change b (a (CommRingCat.KaehlerDifferential.d r)) =
      CommRingCat.KaehlerDifferential.d r
    dsimp only [a, b]
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    congr 1
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      ConcreteCategory.congr_hom e.hom_inv_id r
  have hright : b ≫ (ModuleCat.restrictScalars e.inv.hom).map a ≫ cC.hom = 𝟙 _ := by
    apply CommRingCat.KaehlerDifferential.ext
    intro r
    change a (b (CommRingCat.KaehlerDifferential.d r)) =
      CommRingCat.KaehlerDifferential.d r
    dsimp only [a, b]
    rw [CommRingCat.KaehlerDifferential.map_d, CommRingCat.KaehlerDifferential.map_d]
    congr 1
    simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using
      ConcreteCategory.congr_hom e.inv_hom_id r
  have ha : Function.Bijective a := by
    constructor
    · intro x y hxy
      have hx := ConcreteCategory.congr_hom hleft x
      have hy := ConcreteCategory.congr_hom hleft y
      simpa only [ModuleCat.comp_apply, ModuleCat.id_apply] using
        hx.symm.trans ((congrArg back hxy).trans hy)
    · intro y
      refine ⟨back y, ?_⟩
      have hy := ConcreteCategory.congr_hom hright y
      change a (b y) = y
      change a (b y) = y at hy
      exact hy
  exact (LinearEquiv.ofBijective a.hom ha).toModuleIso

@[simp] lemma actualRingIsoKaehlerComparison_hom_D
    (α : k ⟶ B) (α' : k ⟶ C) (e : B ≅ C) (h : α ≫ e.hom = α') (r : B) :
    (actualRingIsoKaehlerComparison α α' e h).hom
      (CommRingCat.KaehlerDifferential.d r) =
        CommRingCat.KaehlerDifferential.d (e.hom r) := by
  exact CommRingCat.KaehlerDifferential.map_d
    (g := 𝟙 k) (g' := e.hom)
    (by simpa only [Category.id_comp] using h.symm) r

end PfaffianDescent
