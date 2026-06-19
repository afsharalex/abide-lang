use std::cell::RefCell;
use std::collections::HashMap;

// Process-local interning table mapping each distinct string literal to a
// distinct integer id. Using a hash here would be unsound: two different
// strings could collide to the same id, making the SMT backend treat them as
// equal while the concrete evaluators (which compare `String`s exactly)
// distinguish them. An interner is injective by construction, so SMT string
// equality matches the concrete `==`.
//
// Ids are assigned in first-seen order starting at 1 (so a string id is never
// 0). The specific values are irrelevant to soundness — only that the mapping
// is a stable bijection within a process: the same string always yields the
// same id, and distinct strings always yield distinct ids. The id never
// escapes into a witness (witnesses carry the original `String`), so the
// first-seen ordering is invisible to users and to cross-process determinism.
thread_local! {
    static STRING_INTERNER: RefCell<HashMap<String, i64>> = RefCell::new(HashMap::new());
}

/// Encode a string literal into the verifier's current integer-backed string
/// representation.
///
/// Strings are represented as integers while there is no dedicated string
/// theory. The mapping must be **injective** so the encoding agrees with the
/// concrete evaluators' exact string comparison; this is guaranteed by interning
/// rather than hashing.
pub(super) fn string_literal_id(value: &str) -> i64 {
    STRING_INTERNER.with(|interner| {
        let mut map = interner.borrow_mut();
        if let Some(id) = map.get(value) {
            return *id;
        }
        let id = next_string_literal_id(map.len());
        map.insert(value.to_owned(), id);
        id
    })
}

fn next_string_literal_id(interned_count: usize) -> i64 {
    i64::try_from(interned_count).unwrap_or(i64::MAX - 1) + 1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_literal_ids_are_stable_and_distinguish_basic_literals() {
        assert_eq!(string_literal_id("good"), string_literal_id("good"));
        assert_ne!(string_literal_id("good"), string_literal_id("bad"));
        assert_ne!(string_literal_id(""), string_literal_id("bad"));
        assert_ne!(string_literal_id("good"), 0);
    }

    #[test]
    fn string_literal_ids_are_injective_over_a_battery() {
        // Distinct strings must map to distinct ids — a hash could collide and
        // make the solver conflate two different strings, diverging from the
        // concrete `==`. Interning guarantees a bijection.
        let samples = [
            "",
            "a",
            "b",
            "ab",
            "ba",
            "good",
            "bad",
            "Pending",
            "Confirmed",
            "0",
            "1",
            "true",
            "false",
            "null",
            "café",
            "naïve",
            "👍",
            "a\nb",
            "a b",
        ];
        let mut seen: HashMap<i64, &str> = HashMap::new();
        for s in samples {
            let id = string_literal_id(s);
            assert_ne!(id, 0, "string id must never be 0 ({s:?})");
            if let Some(prev) = seen.insert(id, s) {
                panic!("string id collision: {prev:?} and {s:?} both map to {id}");
            }
            // Idempotent: re-encoding the same string yields the same id.
            assert_eq!(string_literal_id(s), id, "id not stable for {s:?}");
        }
    }

    #[test]
    fn string_literal_next_id_saturates_at_max_i64_after_count_overflow() {
        assert_eq!(next_string_literal_id(0), 1);
        assert_eq!(next_string_literal_id(1), 2);
        assert_eq!(next_string_literal_id(usize::MAX), i64::MAX);
    }
}
