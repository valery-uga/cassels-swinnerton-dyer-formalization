import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Abel

/-! # A split decomposition from an actual ground evaluation kernel basis -/
noncomputable section
namespace PfaffianDescent
universe u v w z
set_option backward.isDefEq.respectTransparency false
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]
variable {T : Type z} [AddCommGroup T] [Module F T]

theorem serreIncidenceGroundKernel_split_identity
    (f : V →ₗ[F] W) (l : T →ₗ[F] V) (n : V →ₗ[F] T) (d : W →ₗ[F] V)
    (hl : LinearMap.range l = LinearMap.ker f)
    (hn : n.comp l = LinearMap.id) (hd : f.comp d = LinearMap.id) :
    l.comp n + ((LinearMap.id - l.comp n).comp d).comp f = LinearMap.id := by
  ext x
  have hx : x - d (f x) ∈ LinearMap.ker f := by
    change f (x - d (f x)) = 0
    have hdx := LinearMap.congr_fun hd (f x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hdx
    simp only [map_sub, hdx, sub_self]
  rw [← hl] at hx
  obtain ⟨t, ht⟩ := hx
  have hnt := LinearMap.congr_fun hn t
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hnt
  have hnx : l (n (x - d (f x))) = x - d (f x) := by
    rw [← ht, hnt]
  simp only [map_sub] at hnx
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply]
  calc
    l (n x) + (d (f x) - l (n (d (f x)))) =
        (l (n x) - l (n (d (f x)))) + d (f x) := by abel
    _ = (x - d (f x)) + d (f x) := by rw [hnx]
    _ = x := sub_add_cancel _ _

theorem serreIncidenceGroundKernel_exists_split
    (f : V →ₗ[F] W) (l : T →ₗ[F] V)
    (hl : LinearMap.range l = LinearMap.ker f)
    (hinj : Function.Injective l) (honto : Function.Surjective f) :
    ∃ n : V →ₗ[F] T, ∃ d : W →ₗ[F] V,
      f.comp l = 0 ∧ n.comp l = LinearMap.id ∧
      l.comp n + d.comp f = LinearMap.id := by
  obtain ⟨n, hn⟩ := l.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  obtain ⟨d, hd⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr honto)
  refine ⟨n, (LinearMap.id - l.comp n).comp d, ?_, hn, ?_⟩
  · apply LinearMap.ext
    intro t
    have ht : l t ∈ LinearMap.range l := ⟨t, rfl⟩
    rw [hl] at ht
    exact ht
  · exact serreIncidenceGroundKernel_split_identity f l n d hl hn hd

end PfaffianDescent
