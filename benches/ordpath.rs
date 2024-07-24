use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ordpath::{
    enc::{self, Encoding},
    OneTerminatedPath, OrdPath, ZeroTerminatedPath,
};

fn comparison<E: Encoding, const N: usize, const Z: bool, F: Fn(&[i64]) -> OrdPath<E, N, Z>>(
    c: &mut Criterion,
    f: F,
) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = f(&seq);
        let y = f(&seq);

        c.bench_function(&format!("ordpath_comparison_{}", len), |b| {
            b.iter(|| {
                black_box(x.cmp(&y));
            })
        });
    }
}

fn comparison_zero_term(c: &mut Criterion) {
    comparison(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn comparison_one_term(c: &mut Criterion) {
    comparison(c, |s| <OneTerminatedPath>::from_slice(s, enc::Default));
}

fn from_slice<E: Encoding, const N: usize, const Z: bool, F: Fn(&[i64]) -> OrdPath<E, N, Z>>(
    c: &mut Criterion,
    f: F,
) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len).collect::<Vec<_>>();

        c.bench_function(&format!("ordpath_from_slice_{}", len), |b| {
            b.iter(|| {
                black_box(f(&s));
            })
        });
    }
}

fn from_slice_one_term(c: &mut Criterion) {
    from_slice(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn from_slice_zero_term(c: &mut Criterion) {
    from_slice(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn from_str<E: Encoding, const N: usize, const Z: bool, F: Fn(&str) -> OrdPath<E, N, Z>>(
    c: &mut Criterion,
    f: F,
) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(".");

        c.bench_function(&format!("ordpath_from_str_{}", len), |b| {
            b.iter(|| {
                black_box(f(&s));
            })
        });
    }
}

fn from_str_one_term(c: &mut Criterion) {
    from_str(c, |s| <ZeroTerminatedPath>::from_str(s, enc::Default));
}

fn from_str_zero_term(c: &mut Criterion) {
    from_str(c, |s| <ZeroTerminatedPath>::from_str(s, enc::Default));
}

fn is_ancestor_of<E: Encoding, const N: usize, const Z: bool, F: Fn(&[i64]) -> OrdPath<E, N, Z>>(
    c: &mut Criterion,
    f: F,
) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = f(&seq);
        let y = f(&seq);

        c.bench_function(&format!("ordpath_is_ancestor_of_{}", len), |b| {
            b.iter(|| {
                black_box(x.is_ancestor_of(&y));
            })
        });
    }
}

fn is_ancestor_of_one_term(c: &mut Criterion) {
    is_ancestor_of(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn is_ancestor_of_zero_term(c: &mut Criterion) {
    is_ancestor_of(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn iteration<E: Encoding, const N: usize, const Z: bool, F: Fn(&[i64]) -> OrdPath<E, N, Z>>(
    c: &mut Criterion,
    f: F,
) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len).collect::<Vec<_>>();
        let p = f(&s);

        c.bench_function(&format!("ordpath_iteration{}", len), |b| {
            b.iter(|| {
                for x in &p {
                    black_box(x);
                }
            })
        });
    }
}

fn iteration_one_term(c: &mut Criterion) {
    iteration(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

fn iteration_zero_term(c: &mut Criterion) {
    iteration(c, |s| <ZeroTerminatedPath>::from_slice(s, enc::Default));
}

criterion_group!(
    benches,
    comparison_one_term,
    comparison_zero_term,
    from_slice_one_term,
    from_slice_zero_term,
    from_str_one_term,
    from_str_zero_term,
    is_ancestor_of_one_term,
    is_ancestor_of_zero_term,
    iteration_one_term,
    iteration_zero_term,
);

criterion_main!(benches);
