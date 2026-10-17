import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/- SOURCE ONLY / UNVERIFIED. An auxiliary gluing lemma for actual module
maps. The local linearity input belongs to this generic lemma; its Kaehler
caller must derive it from canonical localization linear equivalences. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {ι : Type u}

/-- The actual section module, at the presheaf's native scalar-ring alias. -/
private instance actualBasisSectionModule (N : X.Modules) (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (N.presheaf.obj U) :=
  (N.val.obj U).isModule

/-- The same actual action after restricting the abelian presheaf to the basis. -/
private instance actualBasisRestrictedSectionModule (N : X.Modules)
    (B : ι → X.Opens) (i : ι) :
    Module (X.ringCatSheaf.obj.obj (op (B i)))
      (((inducedFunctor B).op ⋙ N.presheaf).obj (op i)) :=
  (N.val.obj (op (B i))).isModule

/-- Extend module-linear maps on an actual topological basis to all opens.
The target is a genuine sheaf; the source need only be a presheaf. -/
def modulePresheafHomFromActualBasis
    (P : X.PresheafOfModules) (N : X.Modules)
    (B : ι → X.Opens) (hB : Opens.IsBasis (Set.range B))
    (a : (inducedFunctor B).op ⋙ P.presheaf ⟶
      (inducedFunctor B).op ⋙ N.presheaf)
    (ha : ∀ (i : ι) (r : X.ringCatSheaf.obj.obj (op (B i)))
      (x : P.obj (op (B i))),
      (a.app (op i) (r • x) : N.val.obj (op (B i))) =
        r • (a.app (op i) x : N.val.obj (op (B i)))) : P ⟶ N.val := by
  let Ns : TopCat.Sheaf AddCommGrpCat X := ⟨N.presheaf, N.isSheaf⟩
  let b : P.presheaf ⟶ N.presheaf :=
    TopCat.Sheaf.restrictHomEquivHom P.presheaf Ns hB a
  have hb : ∀ i : ι, b.app (op (B i)) = a.app (op i) := by
    intro i
    exact TopCat.Sheaf.extend_hom_app P.presheaf Ns hB a i
  have hnat {U V : X.Opens} (hVU : V ≤ U) (x : P.obj (op U)) :
      N.val.map (homOfLE hVU).op (b.app (op U) x) =
        b.app (op V) (P.map (homOfLE hVU).op x) := by
    have h := congrArg (fun f => f x) (b.naturality (homOfLE hVU).op)
    exact h.symm
  refine {
    app := fun U => ModuleCat.ofHom {
      toFun := b.app U
      map_add' := (b.app U).hom.map_add
      map_smul' := ?_ }
    naturality := ?_ }
  · intro r x
    apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
    intro y hy
    obtain ⟨V, ⟨i, rfl⟩, hyV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hy
    refine ⟨B i, hVU, hyV, ?_⟩
    calc
      N.val.map (homOfLE hVU).op (b.app U (r • x)) =
          b.app (op (B i)) (P.map (homOfLE hVU).op (r • x)) := hnat hVU _
      _ = a.app (op i)
          (X.ringCatSheaf.obj.map (homOfLE hVU).op r • P.map (homOfLE hVU).op x) := by
            rw [P.map_smul, hb]
            rfl
      _ = X.ringCatSheaf.obj.map (homOfLE hVU).op r •
          a.app (op i) (P.map (homOfLE hVU).op x) := ha i _ _
      _ = X.ringCatSheaf.obj.map (homOfLE hVU).op r •
          N.val.map (homOfLE hVU).op (b.app U x) := by
            rw [hnat, hb]
            rfl
      _ = N.val.map (homOfLE hVU).op (r • b.app U x) :=
        (N.val.map_smul (homOfLE hVU).op r _).symm
  · intro U V f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun h => h x) (b.naturality f)

end PfaffianDescent
