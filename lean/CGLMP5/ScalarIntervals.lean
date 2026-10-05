import CGLMP5.ScalarDefs

/-! Sound rational enclosure arithmetic, independent of certificate data. -/

namespace CGLMP5

/-- Endpoints are rational, and every operation below is executable. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

namespace QInterval

def Contains (q : QInterval) (x : ℝ) : Prop := (q.lo : ℝ) ≤ x ∧ x ≤ (q.hi : ℝ)
def point (q : ℚ) : QInterval := ⟨q,q⟩
def add (a b : QInterval) : QInterval := ⟨a.lo+b.lo,a.hi+b.hi⟩
def scale (q : ℚ) (a : QInterval) : QInterval :=
  if 0 ≤ q then ⟨q*a.lo,q*a.hi⟩ else ⟨q*a.hi,q*a.lo⟩
/-- Multiplication restricted to intervals with nonnegative lower endpoints. -/
def mulPos (a b : QInterval) : QInterval := ⟨a.lo*b.lo,a.hi*b.hi⟩
def powPos (a : QInterval) : ℕ → QInterval
  | 0 => point 1
  | n+1 => mulPos (powPos a n) a

def sum (a : List QInterval) : QInterval := a.foldr add (point 0)

@[simp] lemma contains_point (q : ℚ) : (point q).Contains (q : ℝ) := ⟨le_rfl,le_rfl⟩

lemma contains_add {a b : QInterval} {x y : ℝ} (hx : a.Contains x) (hy : b.Contains y) :
    (add a b).Contains (x+y) := by
  constructor <;> dsimp [add] <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

lemma contains_scale (q : ℚ) {a : QInterval} {x : ℝ} (hx : a.Contains x) :
    (scale q a).Contains ((q:ℝ)*x) := by
  unfold scale
  split_ifs with h
  · have h' : (0:ℝ) ≤ q := by exact_mod_cast h
    constructor <;> dsimp <;> push_cast
    · exact mul_le_mul_of_nonneg_left hx.1 h'
    · exact mul_le_mul_of_nonneg_left hx.2 h'
  · have h' : (q:ℝ) ≤ 0 := by exact_mod_cast le_of_lt (lt_of_not_ge h)
    constructor <;> dsimp <;> push_cast
    · exact mul_le_mul_of_nonpos_left hx.2 h'
    · exact mul_le_mul_of_nonpos_left hx.1 h'

lemma contains_mulPos {a b : QInterval} {x y : ℝ}
    (ha : 0 ≤ a.lo) (hb : 0 ≤ b.lo) (hx : a.Contains x) (hy : b.Contains y) :
    (mulPos a b).Contains (x*y) := by
  have hal : (0:ℝ) ≤ a.lo := by exact_mod_cast ha
  have hbl : (0:ℝ) ≤ b.lo := by exact_mod_cast hb
  have hx0 := hal.trans hx.1
  have hy0 := hbl.trans hy.1
  constructor <;> dsimp [mulPos] <;> push_cast
  · exact mul_le_mul hx.1 hy.1 hbl hx0
  · exact mul_le_mul hx.2 hy.2 hy0 (hx0.trans hx.2)

lemma powPos_lo_nonneg {a : QInterval} (ha : 0 ≤ a.lo) (n : ℕ) :
    0 ≤ (powPos a n).lo := by
  induction n with
  | zero => norm_num [powPos, point]
  | succ n hn => exact mul_nonneg hn ha

lemma contains_powPos {a : QInterval} {x : ℝ} (ha : 0 ≤ a.lo) (hx : a.Contains x)
    (n : ℕ) : (powPos a n).Contains (x^n) := by
  induction n with
  | zero => simpa [powPos] using contains_point 1
  | succ n hn => exact contains_mulPos (powPos_lo_nonneg ha n) ha hn hx

lemma contains_sum {a : List QInterval} {xs : List ℝ}
    (h : List.Forall₂ Contains a xs) : (sum a).Contains xs.sum := by
  induction h with
  | nil => simpa [sum] using contains_point 0
  | cons ha ht ih => exact contains_add ha ih

lemma contains_finset_sum {ι : Type*} (t : Finset ι) (a : ι → QInterval) (v : ι → ℝ)
    (h : ∀ i ∈ t, (a i).Contains (v i)) :
    (⟨∑ i ∈ t, (a i).lo, ∑ i ∈ t, (a i).hi⟩ : QInterval).Contains (∑ i ∈ t, v i) := by
  constructor <;> dsimp <;> push_cast
  · exact Finset.sum_le_sum fun i hi => (h i hi).1
  · exact Finset.sum_le_sum fun i hi => (h i hi).2

end QInterval

lemma mu_mem_of_signs {a b : ℝ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hpa : sextic a < 0) (hpb : 0 < sextic b) : a ≤ mu ∧ mu ≤ b := by
  constructor
  · by_contra hn
    have h := sextic_strictMonoOn (le_of_lt mu_gt_three) ha (lt_of_not_ge hn)
    rw [sextic_mu] at h
    exact (not_lt_of_ge (le_of_lt hpa)) h
  · by_contra hn
    have h := sextic_strictMonoOn hb (le_of_lt mu_gt_three) (lt_of_not_ge hn)
    rw [sextic_mu] at h
    exact (not_lt_of_ge (le_of_lt hpb)) h

namespace Scalar

def basisInterval (sI xI uI : QInterval) (k : Fin 24) : QInterval :=
  if k.val < 12 then
    QInterval.mulPos
      (QInterval.mulPos (sI.powPos (k.val % 2)) (xI.powPos ((k.val/2)%3)))
      (uI.powPos ((k.val/6)%2))
  else QInterval.point 0

lemma basisInterval_contains {sI xI uI : QInterval}
    (hs : sI.Contains s) (hx : xI.Contains x) (hu : uI.Contains u)
    (hs0 : 0 ≤ sI.lo) (hx0 : 0 ≤ xI.lo) (hu0 : 0 ≤ uI.lo) (k : Fin 24) :
    (basisInterval sI xI uI k).Contains
      (if k.val < 12 then realMonomial k else 0) := by
  unfold basisInterval
  split_ifs with hk
  · apply QInterval.contains_mulPos
    · exact mul_nonneg (QInterval.powPos_lo_nonneg hs0 _) (QInterval.powPos_lo_nonneg hx0 _)
    · exact QInterval.powPos_lo_nonneg hu0 _
    · exact QInterval.contains_mulPos
        (QInterval.powPos_lo_nonneg hs0 _) (QInterval.powPos_lo_nonneg hx0 _)
        (QInterval.contains_powPos hs0 hs _) (QInterval.contains_powPos hx0 hx _)
    · exact QInterval.contains_powPos hu0 hu _
  · simpa using QInterval.contains_point 0

def enclosure (sI xI uI : QInterval) (a : Scalar) : QInterval :=
  ⟨∑ k : Fin 24, (QInterval.scale (a k) (basisInterval sI xI uI k)).lo,
   ∑ k : Fin 24, (QInterval.scale (a k) (basisInterval sI xI uI k)).hi⟩

lemma enclosure_contains {sI xI uI : QInterval}
    (hs : sI.Contains s) (hx : xI.Contains x) (hu : uI.Contains u)
    (hs0 : 0 ≤ sI.lo) (hx0 : 0 ≤ xI.lo) (hu0 : 0 ≤ uI.lo) (a : Scalar) :
    (enclosure sI xI uI a).Contains (evalReal a) := by
  rw [evalReal_eq]
  exact QInterval.contains_finset_sum Finset.univ _ _ fun k _ =>
    QInterval.contains_scale _ (basisInterval_contains hs hx hu hs0 hx0 hu0 k)

end Scalar

end CGLMP5
