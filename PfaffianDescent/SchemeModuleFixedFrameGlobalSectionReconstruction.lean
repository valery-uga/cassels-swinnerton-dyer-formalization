import PfaffianDescent.SchemeModuleFixedFrameStalkInjectiveOfLocallyRankOne
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! Genuine global reconstruction from the SAME actual stalk images.
Local germ representatives agree on overlaps by original stalk-map
injectivity; actual sheaf gluing produces the global section. Original
pi/scalars/maps remain fixed. No cohomology or image certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Membership in the ORIGINAL global field image is equivalent to
membership in EVERY ORIGINAL stalk image. Sufficiency uses actual
local representatives, genuine overlap uniqueness and actual sheaf gluing.
Rank-one geometry is the ordinary geometric hypothesis supplying uniqueness;
no range comparison, local/global reconstruction or cohomology is assumed. -/
theorem schemeModuleTopSectionsToFunctionFieldLinearMap_mem_range_iff_stalkRange
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M)
    (C : X.Opens) (hgC : genericPoint X ∈ C)
    (e : M.over C ≅ (SheafOfModules.unit X.ringCatSheaf).over C)
    (f : X.functionField) :
    letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
    f ∈ Set.range (schemeModuleTopSectionsToFunctionFieldLinearMap pi M C hgC e) ↔
      ∀ x : X,
        letI := schemeModuleStalkModule M x
        f ∈ Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e x) := by
  classical
  letI : Nonempty C := ⟨⟨genericPoint X, hgC⟩⟩
  constructor
  · rintro ⟨s, hs⟩ x
    letI := schemeModuleStalkModule M x
    exact ⟨M.presheaf.germ ⊤ x trivial s,
      (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_global_germ pi M C e x s).trans hs⟩
  · intro h
    have hlocal : ∀ x : X, ∃ (U : X.Opens) (hxU : x ∈ U) (s : M.val.obj (op U)),
        letI : Nonempty U := ⟨⟨x, hxU⟩⟩
        (schemeModuleFixedFrameOpenToFunctionFieldLinearMap pi M C e U s : X.functionField) = f := by
      intro x
      letI := schemeModuleStalkModule M x
      obtain ⟨a, ha⟩ := h x
      obtain ⟨U, hxU, s, rfl⟩ := M.presheaf.exists_germ_eq a
      refine ⟨U, hxU, s, ?_⟩
      letI : Nonempty U := ⟨⟨x, hxU⟩⟩
      exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e x U hxU s).symm.trans ha
    choose U hx s hs using hlocal
    let F : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨M.presheaf, M.isSheaf⟩
    have hcover : (⊤ : X.Opens) ≤ ⨆ x, U x := by
      intro x _hx
      simp only [Opens.mem_iSup]
      exact ⟨x, hx x⟩
    have hcompat : ∀ x y,
        M.val.map (homOfLE (show U x ⊓ U y ≤ U x from inf_le_left)).op (s x) =
          M.val.map (homOfLE (show U x ⊓ U y ≤ U y from inf_le_right)).op (s y) := by
      intro x y
      let W : X.Opens := U x ⊓ U y
      apply TopCat.Presheaf.section_ext F W
      intro z hz
      letI : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
      letI : Nonempty (U y) := ⟨⟨y, hx y⟩⟩
      letI : Nonempty W := ⟨⟨z, hz⟩⟩
      letI := schemeModuleStalkModule M z
      let rx : W ⟶ U x := homOfLE (show W ≤ U x from inf_le_left)
      let ry : W ⟶ U y := homOfLE (show W ≤ U y from inf_le_right)
      apply schemeModuleFixedFrameStalkToFunctionFieldLinearMap_injective_of_locallyRankOne
        pi M hM C e z
      have hleft :
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e z
            (M.presheaf.germ W z hz (M.val.map rx.op (s x))) : X.functionField) = f :=
        (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e z W hz _).trans
          ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_restrict pi M C e
            (U := U x) (V := W) rx (s x)).trans (hs x))
      have hright :
          (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e z
            (M.presheaf.germ W z hz (M.val.map ry.op (s y))) : X.functionField) = f :=
        (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e z W hz _).trans
          ((schemeModuleFixedFrameOpenToFunctionFieldLinearMap_restrict pi M C e
            (U := U y) (V := W) ry (s y)).trans (hs y))
      exact hleft.trans hright.symm
    let sf : ∀ x : X, F.obj.obj (op (U x)) := fun x => s x
    have hcompat' : TopCat.Presheaf.IsCompatible F.obj U sf := by
      intro x y
      change M.val.map (homOfLE (show U x ⊓ U y ≤ U x from inf_le_left)).op (s x) =
        M.val.map (homOfLE (show U x ⊓ U y ≤ U y from inf_le_right)).op (s y)
      exact hcompat x y
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤
      (fun x => homOfLE (show U x ≤ ⊤ from le_top)) hcover sf hcompat'
    refine ⟨t, ?_⟩
    let g := genericPoint X
    letI := schemeModuleStalkModule M g
    letI : Nonempty (U g) := ⟨⟨g, hx g⟩⟩
    have hgerm : M.presheaf.germ ⊤ g trivial t =
        M.presheaf.germ (U g) g (hx g) (s g) :=
      (M.presheaf.germ_res_apply (homOfLE (show U g ≤ ⊤ from le_top)) g (hx g) t).symm.trans
        (congrArg (M.presheaf.germ (U g) g (hx g)) (ht g))
    exact (schemeModuleFixedFrameStalkToFunctionFieldLinearMap_global_germ pi M C e g t).symm.trans
      ((congrArg (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C e g) hgerm).trans
        ((schemeModuleFixedFrameStalkToFunctionFieldLinearMap_germ pi M C e g (U g) (hx g) (s g)).trans
          (hs g)))

end PfaffianDescent
