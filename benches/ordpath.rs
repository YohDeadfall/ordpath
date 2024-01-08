use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ordpath::{Default, OrdPath};

fn ordpath_comparison(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = OrdPath::from_slice(&seq, Default {});
        let y = OrdPath::from_slice(&seq, Default {});

        c.bench_function(&format!("ordpath_comparison_{}", len), |b| {
            b.iter(|| {
                black_box(x.cmp(&y));
            })
        });
    }
}

fn ordpath_from_slice(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len).collect::<Vec<_>>();

        c.bench_function(&format!("ordpath_from_slice_{}", len), |b| {
            b.iter(|| {
                black_box(OrdPath::from_slice(&s, Default {}));
            })
        });
    }
}

fn ordpath_from_str(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let s = (0..*len)
            .map(|x| x.to_string())
            .collect::<Vec<_>>()
            .join(".");

        c.bench_function(&format!("ordpath_from_str_{}", len), |b| {
            b.iter(|| {
                black_box(OrdPath::from_str(&s, Default {}).unwrap());
            })
        });
    }
}

fn ordpath_is_ancestor_of(c: &mut Criterion) {
    for len in &[0, 10, 50, 100, 500, 1000] {
        let seq = (0..*len).collect::<Vec<_>>();
        let x = OrdPath::from_slice(&seq, Default {});
        let y = OrdPath::from_slice(&seq, Default {});

        c.bench_function(&format!("ordpath_is_ancestor_of_{}", len), |b| {
            b.iter(|| {
                black_box(x.is_ancestor_of(&y));
            })
        });
    }
}

criterion_group!(
    benches,
    ordpath_comparison,
    ordpath_from_slice,
    ordpath_from_str,
    ordpath_is_ancestor_of
);

criterion_main!(benches);
