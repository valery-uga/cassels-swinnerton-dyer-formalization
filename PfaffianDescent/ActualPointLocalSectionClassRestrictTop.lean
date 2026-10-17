import PfaffianDescent.ActualPointLocalClassTopNormalization

/- SOURCE ONLY / UNVERIFIED. Genuine LOCAL adjunction-unit classes of
restricted global sections equal their SAME original top-section class.
No spanning assertion or source/fiber comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u

lemma actualPointLocalSectionClass_restrictTop
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (z : M.val.obj (op ⊤)) :
    actualPointLocalSectionClass q M U hU
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op z) =
        actualPointLocalSectionClass q M ⊤ (by rfl) z := by
  let P := (Scheme.Modules.pullback q).obj M
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M
  let r : op (⊤ : X.Opens) ⟶ op U := (homOfLE le_top).op
  have hn := ConcreteCategory.congr_hom (eta.mapPresheaf.naturality r) z
  change eta.val.app (op U) (M.val.map r z) =
    P.val.map ((TopologicalSpace.Opens.map q.base).op.map r) (eta.val.app (op ⊤) z) at hn
  unfold actualPointLocalSectionClass
  rw [hn]
  let i := (TopologicalSpace.Opens.map q.base).op.map r
  let t := eqToHom (congrArg op hU)
  let t0 := eqToHom (congrArg op (show q ⁻¹ᵁ (⊤ : X.Opens) = ⊤ from rfl))
  exact (PresheafOfModules.map_comp_apply P.val i t (eta.val.app (op ⊤) z)).symm.trans
    (PresheafOfModules.congr_map_apply P.val (Subsingleton.elim (i ≫ t) t0)
      (eta.val.app (op ⊤) z))

lemma actualPointLocalSectionClass_restrict_unitHom
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤) (v : schemeModuleUnit X ⟶ M) :
    actualPointLocalSectionClass q M U hU
      (M.val.map (homOfLE (show U ≤ ⊤ from le_top)).op
        (v.val.app (op ⊤) (1 : Γ(X, ⊤)))) =
      actualModulePointSectionClass q M v := by
  rw [actualPointLocalSectionClass_restrictTop,
    actualPointLocalSectionClass_top_of_unitHom]

end PfaffianDescent
