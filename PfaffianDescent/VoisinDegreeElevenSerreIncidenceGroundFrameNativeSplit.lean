import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelSplit
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundFrameCoefficientSquare

/-! # The mapped ground frame splits the actual native evaluation equations -/
noncomputable section
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundFrame_native_split
    {K E : Type u} [Field K] [Field E] [Algebra K E]
    (M : Matrix (Fin 9) (Fin 3) K) (N : Matrix (Fin 3) (Fin 9) K)
    (hNM : N * M = 1) (A : Matrix (Fin 6) (Fin 9) E)
    (hrange : LinearMap.range (Matrix.toLin' (M.map (algebraMap K E))) =
      LinearMap.ker (Matrix.toLin' A))
    (honto : Function.Surjective (Matrix.toLin' A)) :
    ∃ D : Matrix (Fin 9) (Fin 6) E,
      A * M.map (algebraMap K E) = 0 ∧
      M.map (algebraMap K E) * N.map (algebraMap K E) + D * A = 1 := by
  let f := Matrix.toLin' A
  let l := Matrix.toLin' (M.map (algebraMap K E))
  let n := Matrix.toLin' (N.map (algebraMap K E))
  have hn : n.comp l = LinearMap.id := by
    rw [← Matrix.toLin'_mul, serreIncidenceGroundFrame_map_leftInverse
      (algebraMap K E) M N hNM, Matrix.toLin'_one]
  obtain ⟨d, hd⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr honto)
  let d' := (LinearMap.id - l.comp n).comp d
  have hs : l.comp n + d'.comp f = LinearMap.id :=
    serreIncidenceGroundKernel_split_identity f l n d hrange hn hd
  have hfl : f.comp l = 0 := by
    apply LinearMap.ext
    intro t
    have ht : l t ∈ LinearMap.range l := ⟨t, rfl⟩
    rw [hrange] at ht
    exact ht
  refine ⟨LinearMap.toMatrix' d', ?_, ?_⟩
  · simpa only [f, l, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', map_zero] using
      congrArg LinearMap.toMatrix' hfl
  · simpa only [f, l, n, map_add, LinearMap.toMatrix'_comp,
      LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hs

end PfaffianDescent
