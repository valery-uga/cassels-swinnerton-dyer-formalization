import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily

/-! # Literal marked maps on a configuration--parameter product chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable {S B X P Q : Scheme.{u}}
variable (b : B ⟶ S) (x : X ⟶ S) (p : P ⟶ S) (v : Q ⟶ P)
variable (marked : Fin 3 → (B ⟶ X)) (hmarked : ∀ i, marked i ≫ x = b)
variable (U : Fin 3 → Scheme.{u}) (u : ∀ i, U i ⟶ X)
variable (markedU : ∀ i, B ⟶ U i) (hu : ∀ i, markedU i ≫ u i = marked i)

def serreIncidenceProductChartToProduct :
    pullback b (v ≫ p) ⟶ pullback b p :=
  pullback.lift (pullback.fst b (v ≫ p))
    (pullback.snd b (v ≫ p) ≫ v) (by
      rw [Category.assoc]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma serreIncidenceProductChartToProduct_fst :
    serreIncidenceProductChartToProduct b p v ≫ pullback.fst b p =
      pullback.fst b (v ≫ p) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma serreIncidenceProductChartToProduct_snd :
    serreIncidenceProductChartToProduct b p v ≫ pullback.snd b p =
      pullback.snd b (v ≫ p) ≫ v := pullback.lift_snd _ _ _

/-- The actual marked chart factor is constructed by the pullback universal
property from the actual marked map and the common parameter projection. -/
def serreIncidenceProductChartMarked (i : Fin 3) :
    pullback b (v ≫ p) ⟶ pullback (u i ≫ x) (v ≫ p) :=
  pullback.lift (pullback.fst b (v ≫ p) ≫ markedU i)
    (pullback.snd b (v ≫ p)) (by
      rw [Category.assoc, ← Category.assoc (markedU i), hu i, hmarked i]
      exact pullback.condition)

@[reassoc (attr := simp)]
lemma serreIncidenceProductChartMarked_fst (i : Fin 3) :
    serreIncidenceProductChartMarked b x p v marked hmarked U u markedU hu i ≫
      pullback.fst (u i ≫ x) (v ≫ p) =
      pullback.fst b (v ≫ p) ≫ markedU i := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma serreIncidenceProductChartMarked_snd (i : Fin 3) :
    serreIncidenceProductChartMarked b x p v marked hmarked U u markedU hu i ≫
      pullback.snd (u i ≫ x) (v ≫ p) =
      pullback.snd b (v ≫ p) := pullback.lift_snd _ _ _

/-- The constructed chart factor is exactly the actual marked incidence map
restricted to the chosen parameter chart. -/
theorem serreIncidenceProductChartMarked_comp (i : Fin 3) :
    serreIncidenceProductChartMarked b x p v marked hmarked U u markedU hu i ≫
      pullback.map (u i ≫ x) (v ≫ p) x p (u i) v (𝟙 S)
        (by simp) (by simp) =
    serreIncidenceProductChartToProduct b p v ≫
      fixedLinearSystemIncidenceMap b x p marked hmarked i := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst,
      serreIncidenceProductChartMarked_fst_assoc,
      fixedLinearSystemIncidenceMap, pullback.lift_fst,
      serreIncidenceProductChartToProduct_fst_assoc]
    exact congrArg (fun t => pullback.fst b (v ≫ p) ≫ t) (hu i)
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      serreIncidenceProductChartMarked_snd_assoc,
      fixedLinearSystemIncidenceMap, pullback.lift_snd,
      serreIncidenceProductChartToProduct_snd]

end
end PfaffianDescent
