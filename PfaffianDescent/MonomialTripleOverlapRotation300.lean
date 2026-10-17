import PfaffianDescent.MonomialWholeIdealOverlapSymmetry293

noncomputable section
namespace PfaffianDescent
universe u v
variable {A : Type u} [CommRing A] {m n : ℕ}
variable (B C D : Fin n → (Fin m →₀ ℕ))

/-- Triple rotation is defined on the same literal whole ideal. Both needed
new monomial bases are derived from the original triple determinant units. -/
def monomialTripleOverlapRotate300
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    MonomialWholeIdealTripleOverlap293 (A := A) C D B := by
  refine ⟨monomialTripleOverlapSecondLast293 B C D x, ?_⟩
  exact (monomialWholeIdealOverlapFlip293 B C x.val).property

lemma monomialTripleOverlapRotate_ideal300
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    (monomialTripleOverlapRotate300 B C D x).val.val.val = x.val.val.val := rfl

lemma monomialTripleOverlapRotate_cycle300
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    monomialTripleOverlapRotate300 D B C
        (monomialTripleOverlapRotate300 C D B (monomialTripleOverlapRotate300 B C D x)) = x := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- The actual triple datum maps along an arbitrary original coefficient map;
its two determinant unit conditions are transported, not assumed. -/
def monomialTripleOverlapMap300
    {E : Type v} [CommRing E] (kB : Fin n) (hkB : B kB = 0)
    (f : A →+* E) (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    MonomialWholeIdealTripleOverlap293 (A := E) B C D := by
  refine ⟨monomialWholeIdealChartOverlapMap290 B C kB hkB f x.val, ?_⟩
  change IsUnit (monomialWholeIdealChartTransitionDet290 B D
    (monomialWholeIdealChartMap287 B kB hkB f x.val.val))
  rw [monomialWholeIdealChartTransitionDet_map290 B D kB hkB f x.val.val]
  exact x.property.map f

lemma monomialTripleOverlapFirstLast_natural300
    {E : Type v} [CommRing E] (kB : Fin n) (hkB : B kB = 0)
    (f : A →+* E) (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    monomialTripleOverlapFirstLast293 B C D (monomialTripleOverlapMap300 B C D kB hkB f x) =
      monomialWholeIdealChartOverlapMap290 B D kB hkB f
        (monomialTripleOverlapFirstLast293 B C D x) := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma monomialTripleOverlapRotate_natural300
    {E : Type v} [CommRing E] (kB kC : Fin n) (hkB : B kB = 0) (hkC : C kC = 0)
    (f : A →+* E) (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    monomialTripleOverlapRotate300 B C D (monomialTripleOverlapMap300 B C D kB hkB f x) =
      monomialTripleOverlapMap300 C D B kC hkC f (monomialTripleOverlapRotate300 B C D x) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rfl

lemma monomialTripleOverlapRotate_firstLast300
    (x : MonomialWholeIdealTripleOverlap293 (A := A) B C D) :
    monomialTripleOverlapFirstLast293 C D B (monomialTripleOverlapRotate300 B C D x) =
      monomialWholeIdealOverlapFlip293 B C x.val := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

end PfaffianDescent
