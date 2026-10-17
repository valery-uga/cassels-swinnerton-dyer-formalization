import Mathlib.AlgebraicGeometry.Gluing

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u v

/-- Replace actual open-cover components by genuine presentation Isos, retaining native maps. -/
def nativeSchemeOpenCoverIsoCharts300 {X : Scheme.{u}} (C : Scheme.OpenCover.{v} X)
    (Y : C.I₀ → Scheme.{u}) (e : ∀ i, Y i ≅ C.X i) : Scheme.OpenCover.{v} X :=
  Scheme.Cover.mkOfCovers C.I₀ Y (fun i => (e i).hom ≫ C.f i)
    (fun x => by
      obtain ⟨i, y, hy⟩ := C.exists_eq x
      refine ⟨i, (e i).inv y, ?_⟩
      rw [Scheme.Hom.comp_apply]
      have he : (e i).hom ((e i).inv y) = y := by
        rw [← Scheme.Hom.comp_apply, (e i).inv_hom_id]
        rfl
      rw [he]
      exact hy)
    (fun i => by infer_instance)

lemma nativeSchemeOpenCoverIsoCharts_map300 {X : Scheme.{u}} (C : Scheme.OpenCover.{v} X)
    (Y : C.I₀ → Scheme.{u}) (e : ∀ i, Y i ≅ C.X i) (i : C.I₀) :
    (nativeSchemeOpenCoverIsoCharts300 C Y e).f i = (e i).hom ≫ C.f i := rfl

end PfaffianDescent
