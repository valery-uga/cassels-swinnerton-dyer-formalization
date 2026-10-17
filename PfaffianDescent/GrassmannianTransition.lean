import PfaffianDescent.GrassmannianGraph

namespace PfaffianDescent
section
variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- The first coordinate block of a graph after an ambient coordinate change. -/
def graphTransitionFirst (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N) : M →ₗ[R] M :=
  (LinearMap.fst R M N).comp (e.toLinearMap.comp (LinearMap.id.prod f))

/-- The second coordinate block of the same changed graph. -/
def graphTransitionSecond (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N) : M →ₗ[R] N :=
  (LinearMap.snd R M N).comp (e.toLinearMap.comp (LinearMap.id.prod f))

/-- A Grassmannian transition normalizes the invertible first block to the identity. -/
noncomputable def graphTransition (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (h : Function.Bijective (graphTransitionFirst e f)) : M →ₗ[R] N :=
  (graphTransitionSecond e f).comp (LinearEquiv.ofBijective (graphTransitionFirst e f) h).symm.toLinearMap

lemma graphTransition_apply_first (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (h : Function.Bijective (graphTransitionFirst e f)) (a : M) :
    graphTransition e f h (graphTransitionFirst e f a) = graphTransitionSecond e f a := by
  change graphTransitionSecond e f
    ((LinearEquiv.ofBijective (graphTransitionFirst e f) h).symm
      ((LinearEquiv.ofBijective (graphTransitionFirst e f) h) a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The transition represents the same actual submodule in the changed ambient coordinates. -/
theorem graphTransition_map_graph (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (h : Function.Bijective (graphTransitionFirst e f)) :
    f.graph.map e.toLinearMap = (graphTransition e f h).graph := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hb, rfl⟩
    change b = f a at hb
    subst b
    exact (graphTransition_apply_first e f h a).symm
  · intro hx
    change x.2 = graphTransition e f h x.1 at hx
    obtain ⟨a, ha⟩ := h.surjective x.1
    refine ⟨(a, f a), rfl, ?_⟩
    apply Prod.ext
    · exact ha
    · change graphTransitionSecond e f a = x.2
      rw [← graphTransition_apply_first e f h, ha, hx]

/-- A changed graph belongs to the other standard chart precisely when its
first block is invertible. The statement includes rings with nilpotents. -/
theorem graphTransition_overlap_iff (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N) :
    Function.Bijective (graphTransitionFirst e f) ↔
      Function.Bijective (graphChartQuotientMap (f.graph.map e.toLinearMap)) := by
  constructor
  · intro h
    rw [graphTransition_map_graph e f h]
    exact graphChartQuotientMap_graph_bijective _
  · intro h
    obtain ⟨g, hg, _⟩ := (graphChartQuotientMap_bijective_iff _).mp h
    have hm (a : M) : e (a, f a) ∈ g.graph := by
      rw [← hg]
      exact ⟨(a, f a), rfl, rfl⟩
    constructor
    · intro a b hab
      have he : e (a, f a) = e (b, f b) := by
        apply Prod.ext
        · exact hab
        · exact (hm a).trans ((congrArg g hab).trans (hm b).symm)
      exact congrArg Prod.fst (e.injective he)
    · intro a
      have hm' : (a, g a) ∈ f.graph.map e.toLinearMap := by rw [hg]; rfl
      obtain ⟨⟨b, c⟩, hc, hbc⟩ := hm'
      change c = f b at hc
      subst c
      exact ⟨b, congrArg Prod.fst hbc⟩

lemma linearMap_graph_injective : Function.Injective (LinearMap.graph : (M →ₗ[R] N) → _) := by
  intro f g h
  ext a
  have hm : (a, f a) ∈ g.graph := h ▸ (show (a, f a) ∈ f.graph from rfl)
  exact hm

/-- The changed graph embedding factors through the normalized graph embedding. -/
lemma graphTransition_embedding (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f)) :
    e.toLinearMap.comp (LinearMap.id.prod f) =
      (LinearMap.id.prod (graphTransition e f he)).comp (graphTransitionFirst e f) := by
  apply LinearMap.ext
  intro a
  apply Prod.ext
  · rfl
  · exact (graphTransition_apply_first e f he a).symm

lemma graphTransitionFirst_comp (e d : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f)) :
    graphTransitionFirst (e.trans d) f =
      (graphTransitionFirst d (graphTransition e f he)).comp (graphTransitionFirst e f) := by
  apply LinearMap.ext
  intro a
  exact congrArg (fun x => (d x).1)
    (LinearMap.congr_fun (graphTransition_embedding e f he) a)

/-- The third overlap condition follows from the first two. -/
lemma graphTransition_comp_overlap (e d : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f))
    (hd : Function.Bijective (graphTransitionFirst d (graphTransition e f he))) :
    Function.Bijective (graphTransitionFirst (e.trans d) f) := by
  rw [graphTransitionFirst_comp e d f he]
  exact hd.comp he

/-- The reverse transition is defined at every point of the overlap. -/
lemma graphTransition_inverse_overlap (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f)) :
    Function.Bijective (graphTransitionFirst e.symm (graphTransition e f he)) := by
  apply (graphTransition_overlap_iff _ _).mpr
  rw [← graphTransition_map_graph e f he, ← Submodule.map_comp]
  have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [hcomp, Submodule.map_id]
  exact graphChartQuotientMap_graph_bijective f

/-- Changing coordinates and changing back recovers the original graph matrix. -/
theorem graphTransition_inverse (e : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f)) :
    graphTransition e.symm (graphTransition e f he) (graphTransition_inverse_overlap e f he) = f := by
  apply linearMap_graph_injective
  rw [← graphTransition_map_graph, ← graphTransition_map_graph, ← Submodule.map_comp]
  have hcomp : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  rw [hcomp, Submodule.map_id]

/-- Transitions obey the cocycle identity wherever all three chart expressions exist. -/
theorem graphTransition_cocycle (e d : (M × N) ≃ₗ[R] (M × N)) (f : M →ₗ[R] N)
    (he : Function.Bijective (graphTransitionFirst e f))
    (hd : Function.Bijective (graphTransitionFirst d (graphTransition e f he)))
    (hed : Function.Bijective (graphTransitionFirst (e.trans d) f)) :
    graphTransition d (graphTransition e f he) hd = graphTransition (e.trans d) f hed := by
  apply linearMap_graph_injective
  rw [← graphTransition_map_graph, ← graphTransition_map_graph,
    ← graphTransition_map_graph, ← Submodule.map_comp]
  rfl

end
end PfaffianDescent
