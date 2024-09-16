use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ordpath::{DefaultEncoding, OrdPath};

fn comparison(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = <OrdPath>::from_ordinals(&seq, DefaultEncoding);
        let y = <OrdPath>::from_ordinals(&seq, DefaultEncoding);

        c.bench_function(&format!("ordpath_comparison_{}", len), |b| {
            b.iter(|| {
                black_box(x.cmp(&y));
            })
        });
    }
}

fn from_slice(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len).collect::<Vec<_>>();

        c.bench_function(&format!("ordpath_from_slice_{}", len), |b| {
            b.iter(|| {
                black_box(<OrdPath>::from_ordinals(&s, DefaultEncoding));
            })
        });
    }
}

fn from_str(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(".");

        c.bench_function(&format!("ordpath_from_str_{}", len), |b| {
            b.iter(|| {
                black_box(<OrdPath>::from_str(&s, DefaultEncoding));
            })
        });
    }
}

fn is_ancestor_of(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = <OrdPath>::from_ordinals(&seq, DefaultEncoding);
        let y = <OrdPath>::from_ordinals(&seq, DefaultEncoding);

        c.bench_function(&format!("ordpath_is_ancestor_of_{}", len), |b| {
            b.iter(|| {
                black_box(x.is_ancestor_of(&y));
            })
        });
    }
}

fn iteration(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len).collect::<Vec<_>>();
        let p = <OrdPath>::from_ordinals(&s, DefaultEncoding);

        c.bench_function(&format!("ordpath_iteration{}", len), |b| {
            b.iter(|| {
                for x in &p {
                    black_box(x);
                }
            })
        });
    }
}

criterion_group!(
    benches,
    comparison,
    from_slice,
    from_str,
    is_ancestor_of,
    iteration,
);

criterion_main!(benches);
