# tunadb SQL Semantics

This document is the authoritative reference for SQL semantics in tunadb. When implementing any expression, plan node, or runtime evaluator, these rules take precedence over any prior behaviour. The semantics follow PostgreSQL except where explicitly noted.

---

## 1. Type System

### 1.1 Primitive types

| Type     | Rust type | Description                        |
|----------|-----------|------------------------------------|
| `NULL`   | —         | Absence of a value. Used only as a type-level sentinel during analysis; not a storable column type. |
| `BOOL`   | `bool`    | Boolean: `true` or `false`         |
| `INT`    | `i32`     | 32-bit signed integer              |
| `BIGINT` | `i64`     | 64-bit signed integer              |
| `FLOAT`  | `f32`     | 32-bit IEEE 754 floating point     |
| `DOUBLE` | `f64`     | 64-bit IEEE 754 floating point     |
| `TEXT`   | `String`  | UTF-8 string of arbitrary length   |

### 1.2 Type vs nullability

Every expression has two independent properties: a **static type** and a **nullability flag**. A `BOOL` column can be nullable. A `NULL` literal has type `NULL` and is always nullable. The static type is determined at analysis time; nullability propagates according to the rules in Section 2.

---

## 2. NULL Semantics

### 2.1 NULL is unknown

NULL represents an unknown value. It is not a value itself. No assumption can be made about what a NULL value would be if it were known.

### 2.2 NULL propagation in expressions

Any arithmetic or comparison operation with a NULL operand produces NULL at runtime. The static type is still inferred from the non-null operands (see Section 3.2). This means analysis can always determine a result type even when inputs may be NULL at runtime.

### 2.3 Equality and NULL

`x = NULL` is always NULL, never TRUE or FALSE. This follows from Rule 2.2: comparing an unknown value to anything yields an unknown result. To test whether a value is NULL, use `IS NULL` or `IS NOT NULL` (Section 7).

### 2.4 IS NULL and IS NOT NULL

`NULL IS NULL` → `TRUE`. `NULL IS NOT NULL` → `FALSE`. These are the only expressions that produce a definite non-NULL result from a NULL input.

### 2.5 Nullability propagation table

| Expression                                | nullable?                              |
|-------------------------------------------|----------------------------------------|
| `+`, `-`, `*`, `/` (binary)               | `left.nullable OR right.nullable`      |
| `=`, `<>`, `<`, `>`, `<=`, `>=`          | `left.nullable OR right.nullable`      |
| `AND`                                     | `left.nullable OR right.nullable`      |
| `OR`                                      | `left.nullable OR right.nullable`      |
| `NOT expr`                                | `expr.nullable`                        |
| `CAST(x AS T)`                            | `x.nullable`                           |
| `IS NULL`, `IS NOT NULL`                  | always `false`                         |
| `x AS alias`                              | `x.nullable`                           |
| Unary `+`, unary `-`                      | `child.nullable`                       |
| Column reference                          | from column definition                 |
| Literals (`1`, `'text'`, `true`, …)      | always `false`                         |
| `NULL` literal                            | always `true`                          |

### 2.6 Three-valued logic for AND / OR

**AND truth table:**

| AND       | TRUE  | FALSE     | NULL  |
|-----------|-------|-----------|-------|
| **TRUE**  | TRUE  | FALSE     | NULL  |
| **FALSE** | FALSE | FALSE     | FALSE |
| **NULL**  | NULL  | **FALSE** | NULL  |

`FALSE AND NULL = FALSE` because one false operand makes the conjunction false regardless of the other.

**OR truth table:**

| OR        | TRUE      | FALSE | NULL  |
|-----------|-----------|-------|-------|
| **TRUE**  | TRUE      | TRUE  | TRUE  |
| **FALSE** | TRUE      | FALSE | NULL  |
| **NULL**  | **TRUE**  | NULL  | NULL  |

`TRUE OR NULL = TRUE` because one true operand makes the disjunction true regardless of the other.

The bold cells are short-circuit results where one operand dominates. These apply at runtime. The type system does not track short-circuit behaviour — nullability is always conservatively propagated at analysis time.

### 2.7 Filter / WHERE and NULL

A `WHERE` or `FILTER` clause passes a row if and only if the predicate evaluates to `TRUE`. Rows where the predicate evaluates to `NULL` or `FALSE` are excluded.

---

## 3. Implicit Type Promotion

Implicit promotion happens automatically during analysis when operand types differ. It **only widens — it never narrows**. If no implicit promotion path exists, analysis fails with a type error and the user must write an explicit `CAST`.

### 3.1 Numeric widening order

```
DOUBLE > FLOAT > BIGINT > INT
```

For any binary operation between two numeric types, the result type is the wider of the two.

### 3.2 NULL in arithmetic — type inference

`NULL op T` and `T op NULL` both infer result type `T` statically. At runtime the result is NULL. `NULL op NULL` infers type `NULL`.

### 3.3 Division result types — integer division

Integer division truncates toward zero: `7 / 2 = 3`, `-7 / 2 = -3`.

| Left              | Right             | Result  |
|-------------------|-------------------|---------|
| `INT`             | `INT`             | `INT`   |
| `BIGINT`          | `INT`             | `BIGINT`|
| `INT`             | `BIGINT`          | `BIGINT`|
| `BIGINT`          | `BIGINT`          | `BIGINT`|
| `FLOAT`           | any numeric       | `FLOAT` |
| any numeric       | `FLOAT`           | `FLOAT` |
| `DOUBLE`          | any numeric       | `DOUBLE`|
| any numeric       | `DOUBLE`          | `DOUBLE`|
| `NULL`            | `T`               | `T`     |
| `T`               | `NULL`            | `T`     |
| `NULL`            | `NULL`            | `NULL`  |

To obtain a fractional result from integer operands, cast explicitly: `CAST(x AS DOUBLE) / y`.

### 3.4 Implicit promotion is numeric-only

`TEXT` cannot be implicitly promoted to or from any other type. `BOOL` cannot be implicitly promoted to or from any other type. Mixed-type comparisons or arithmetic involving `TEXT` or `BOOL` require explicit `CAST`.

---

## 4. Explicit Casts — `CAST(x AS T)`

Explicit casts are a user instruction to convert a value. They are validated at analysis time for plausibility. Widening casts always succeed at runtime. Narrowing casts are checked at analysis and may fail at runtime if the value is out of range or unparseable.

### 4.1 Widening casts — always succeed at runtime

```
INT    → BIGINT, FLOAT, DOUBLE, TEXT
BIGINT → FLOAT, DOUBLE, TEXT
FLOAT  → DOUBLE, TEXT
DOUBLE → TEXT
BOOL   → TEXT  ('true' / 'false')
NULL   → any type  (result is NULL with the target type)
```

### 4.2 Narrowing casts — validated at analysis, may fail at runtime

```
BIGINT → INT       fails if value is outside i32 range
DOUBLE → FLOAT     may lose precision (always succeeds, no runtime error)
DOUBLE → BIGINT    truncates toward zero; fails if outside i64 range
DOUBLE → INT       truncates toward zero; fails if outside i32 range
FLOAT  → BIGINT    truncates toward zero; fails if outside i64 range
FLOAT  → INT       truncates toward zero; fails if outside i32 range
TEXT   → INT       fails if not a valid integer string
TEXT   → BIGINT    fails if not a valid integer string
TEXT   → FLOAT     fails if not a valid float string
TEXT   → DOUBLE    fails if not a valid float string
TEXT   → BOOL      accepts 'true'/'false' case-insensitively; fails otherwise
```

### 4.3 Invalid casts

Any cast not listed in 4.1 or 4.2 is rejected at analysis time with a type error.

### 4.4 String concatenation and TEXT casts

The `||` operator requires both operands to be `TEXT`. To concatenate a non-text value, cast it explicitly: `CAST(count AS TEXT) || ' rows'`. This is intentionally stricter than PostgreSQL's implicit-cast behaviour and may be relaxed in a future version.

---

## 5. Comparison Operators

### 5.1 Operators

`=`, `<>`, `!=`, `<`, `>`, `<=`, `>=`

`<>` and `!=` are both accepted as not-equals operators and are interchangeable.

### 5.2 Type compatibility

Both operands must have compatible types. If they differ and a numeric widening path exists (Section 3.1), the narrower operand is implicitly widened to match the wider type. Analysis inserts an implicit `CAST` node. If the types are incompatible (e.g. `TEXT` vs `INT`), a type error is raised and the user must write an explicit `CAST`.

### 5.3 Result type and nullability

The result type of any comparison is always `BOOL`. The result is nullable if either operand is nullable, because a NULL operand produces a NULL result (Rule 2.2).

### 5.4 Comparing with NULL

`x = NULL` is always NULL (not FALSE). Use `IS NULL` to test for NULL.

### 5.5 TEXT comparisons

`TEXT` values are compared lexicographically by byte value (UTF-8 order).

### 5.6 BOOL comparisons

`BOOL` values are comparable: `FALSE < TRUE`.

---

## 6. Logical Operators

### 6.1 AND, OR, NOT

Operands of `AND`, `OR`, and `NOT` must be of type `BOOL`. Operands with a nullable `BOOL` type are accepted; the NULL value is handled at runtime per the three-valued logic tables in Section 2.6.

### 6.2 Result type

Always `BOOL`.

### 6.3 Nullability

Propagates as defined in Section 2.5.

### 6.4 NOT truth table

| Input | Result |
|-------|--------|
| TRUE  | FALSE  |
| FALSE | TRUE   |
| NULL  | NULL   |

---

## 7. IS NULL / IS NOT NULL

### 7.1 IS NULL

`x IS NULL` returns `TRUE` if `x` evaluates to NULL, `FALSE` otherwise. The result is always a non-nullable `BOOL`.

### 7.2 IS NOT NULL

`x IS NOT NULL` returns `TRUE` if `x` is not NULL, `FALSE` if it is NULL. The result is always a non-nullable `BOOL`.

### 7.3 Always non-nullable

These are the only expressions that consume a potentially nullable input and always produce a non-null result.

---

## 8. Arithmetic Operators

### 8.1 Operators

Binary: `+`, `-`, `*`, `/`. Unary: `+`, `-`.

### 8.2 Operand types

Operands must be numeric (`INT`, `BIGINT`, `FLOAT`, `DOUBLE`) or `NULL`. Mixed numeric types are promoted per Section 3.1. Non-numeric operands are a type error.

### 8.3 Result type

Follows Sections 3.1–3.3.

### 8.4 Integer overflow

Integer overflow is a **runtime error**. There is no silent wrapping.

### 8.5 Division by zero

Division by zero is a **runtime error** for both integer and float operands. IEEE 754 Inf and NaN are not produced by division — see Section 8.6 for how NaN from other sources is handled.

### 8.6 NaN

NaN can arise from float operations such as `0.0 / 0.0` only if explicitly cast from a string (`CAST('NaN' AS DOUBLE)`). Arithmetic with NaN propagates NaN. Comparisons involving NaN:

- `NaN = NaN` → `TRUE`
- `NaN <> NaN` → `FALSE`
- `NaN > x` → `TRUE` for all non-NaN `x`
- `NaN < x` → `FALSE` for all non-NaN `x`

NaN is ordered greater than all non-NaN values. This matches PostgreSQL and deviates from IEEE 754 in order to give NaN a stable, consistent position in sort order and index structures.

---

## 9. String Concatenation

### 9.1 Operator

`x || y` concatenates two `TEXT` values. The result type is `TEXT`.

### 9.2 NULL propagation

If either operand is NULL, the result is NULL.

### 9.3 Type requirement

Both operands must be `TEXT`. To concatenate a non-text value, cast it explicitly:

```sql
CAST(123 AS TEXT) || ' items'
```

This is intentionally stricter than PostgreSQL's behaviour (which auto-casts to text). It may be relaxed in a future version.

---

## 10. Number Literals

### 10.1 Integer literals

An integer literal that fits in `i32` range is parsed as `INT`. One that requires more than 32 bits is parsed as `BIGINT`. A value that overflows `i64` is a parse error.

### 10.2 Float literals

Any literal containing a decimal point or exponent (`1.0`, `1e3`, `1.5e-2`) is parsed as `DOUBLE`. There is no implicit `FLOAT` literal. To produce a `FLOAT` value, use an explicit cast:

```sql
CAST(1.0 AS FLOAT)
```

### 10.3 Unary minus on literals

In expression context, `-` is always parsed as the unary minus operator applied to the following primary expression. It is not folded into the literal at parse time. The result is `UnaryMinus(literal)` which the analyser may constant-fold. This means `-2147483648` is `UnaryMinus(LiteralBigInt(2147483648))` and has type `BIGINT`, not `INT`.

---

## 11. INSERT Type Compatibility

### 11.1 Column assignment rules

When inserting a value of type `S` into a column of type `T`:

- `S = T` → allowed
- `S` implicitly widens to `T` (Section 3.1, widening only) → allowed without explicit cast
- `S` is `NULL` → allowed into any **nullable** column; rejected at runtime for `NOT NULL` columns
- Otherwise → rejected at analysis time; user must write `CAST(expr AS T)`

### 11.2 Column count

The number of value expressions must exactly match the number of named columns.

---

## 12. Filter / WHERE

### 12.1 Type requirement

The filter expression must have static type `BOOL` after type resolution. A non-`BOOL` expression is a type error.

### 12.2 Runtime NULL exclusion

At runtime, a row passes the filter only when the expression evaluates to `TRUE`. Rows where the predicate evaluates to `NULL` or `FALSE` are excluded (Rule 2.7). A nullable `BOOL` expression is valid in a filter — NULL rows are simply excluded at runtime.

---

## 13. Identifiers and Name Resolution

### 13.1 Case normalisation

Unquoted identifiers are case-insensitive and normalised to lowercase during parsing.

### 13.2 Quoted identifiers

Identifiers wrapped in double quotes (`"My Column"`) are case-sensitive and preserve their original casing. A literal double-quote inside a quoted identifier is escaped by doubling it: `"say ""hello"""`.

### 13.3 Resolution

Identifier resolution follows the output schema of the child plan node. An identifier that matches zero columns is an unresolved expression error. An identifier that matches more than one column is an ambiguity error.

---

## 14. Subqueries and Aliases

### 14.1 Default subquery alias

A subquery without an explicit alias is assigned the internal alias `__subquery__`.

### 14.2 Column qualification

Column references into a subquery must be qualified with the subquery alias when ambiguity exists between the outer and inner scopes.

---

## Appendix: PostgreSQL Compatibility Notes

tunadb follows PostgreSQL semantics with the following intentional differences:

| Topic | tunadb | PostgreSQL | Rationale |
|-------|--------|-----------|-----------|
| `\|\|` operand types | Both must be `TEXT`; explicit cast required | Auto-casts any type to text | Simplicity; may be relaxed later |
| NaN in comparisons | `NaN = NaN → TRUE`, NaN sorts greatest | Same | Intentional alignment with PostgreSQL (deviation from IEEE 754) |
| Float division by zero | Runtime error | Runtime error | Intentional alignment with PostgreSQL (deviation from IEEE 754) |
