import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Restrict

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u v
section
variable {X Y : Scheme.{u}} {ι : Type v}
    (U : X.Opens) (V : ι → X.Opens) (hV : ∀ i, V i ≤ U) (hcover : U ≤ ⨆ i, V i)

/-- An open cover expressed using opens of the ambient scheme. -/
noncomputable def schemeOpenSubcover (hcover : U ≤ ⨆ i, V i) : U.toScheme.OpenCover where
  I₀ := ι
  X i := (V i).toScheme
  f i := X.homOfLE (hV i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover x.property)
    refine ⟨i, ⟨x.val, hi⟩, ?_⟩
    apply Subtype.ext
    exact congrArg (fun f : (V i).toScheme ⟶ X => f ⟨x.val, hi⟩)
      (Scheme.homOfLE_ι X (hV i))

include hcover

/-- Morphisms on opens of an ambient scheme glue uniquely when they agree on intersections. -/
theorem schemeOpenMorphisms_glue (f : ∀ i, (V i).toScheme ⟶ Y)
    (hf : ∀ i j, X.homOfLE (show V i ⊓ V j ≤ V i from inf_le_left) ≫ f i =
      X.homOfLE (show V i ⊓ V j ≤ V j from inf_le_right) ≫ f j) :
    ∃! g : U.toScheme ⟶ Y, ∀ i, X.homOfLE (hV i) ≫ g = f i := by
  let C := schemeOpenSubcover U V hV hcover
  have hc : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ f i =
      pullback.snd (C.f i) (C.f j) ≫ f j := by
    intro i j
    let H := isPullback_opens_inf_le (hV i) (hV j)
    apply (cancel_epi H.isoPullback.hom).mp
    exact (Category.assoc H.isoPullback.hom (pullback.fst (C.f i) (C.f j)) (f i)).symm.trans
      ((congrArg (fun a => a ≫ f i) H.isoPullback_hom_fst).trans
        ((hf i j).trans ((congrArg (fun a => a ≫ f j) H.isoPullback_hom_snd).symm.trans
          (Category.assoc H.isoPullback.hom (pullback.snd (C.f i) (C.f j)) (f j)))))
  refine ⟨C.glueMorphisms f hc, fun i => C.ι_glueMorphisms f hc i, ?_⟩
  intro g hg
  apply C.hom_ext
  intro i
  exact (hg i).trans (C.ι_glueMorphisms f hc i).symm

/-- Morphisms out of an open subscheme can be compared on an ambient open cover. -/
lemma schemeOpenMorphisms_ext (f g : U.toScheme ⟶ Y)
    (h : ∀ i, X.homOfLE (hV i) ≫ f = X.homOfLE (hV i) ≫ g) : f = g :=
  (schemeOpenSubcover U V hV hcover).hom_ext f g h

end
end PfaffianDescent
