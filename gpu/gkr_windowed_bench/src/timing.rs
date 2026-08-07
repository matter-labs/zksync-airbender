#[derive(Clone, Debug, PartialEq)]
pub struct TimingSummary {
    pub samples_ms: Vec<f32>,
    pub minimum_ms: f32,
    pub median_ms: f32,
}

pub fn summarize_samples(samples_ms: Vec<f32>) -> Result<TimingSummary, &'static str> {
    if samples_ms.is_empty() {
        return Err("at least one timing sample is required");
    }
    let mut sorted = samples_ms.clone();
    sorted.sort_by(f32::total_cmp);
    let middle = sorted.len() / 2;
    let median_ms = if sorted.len().is_multiple_of(2) {
        (sorted[middle - 1] + sorted[middle]) * 0.5
    } else {
        sorted[middle]
    };
    Ok(TimingSummary {
        minimum_ms: sorted[0],
        median_ms,
        samples_ms,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn odd_sample_summary_uses_the_middle_measurement() {
        let summary = summarize_samples(vec![3.0, 1.0, 2.0]).unwrap();
        assert_eq!(summary.minimum_ms, 1.0);
        assert_eq!(summary.median_ms, 2.0);
        assert_eq!(summary.samples_ms, vec![3.0, 1.0, 2.0]);
    }

    #[test]
    fn even_sample_summary_averages_the_middle_pair() {
        let summary = summarize_samples(vec![4.0, 1.0, 3.0, 2.0]).unwrap();
        assert_eq!(summary.minimum_ms, 1.0);
        assert_eq!(summary.median_ms, 2.5);
    }

    #[test]
    fn empty_sample_summary_is_rejected() {
        assert!(summarize_samples(Vec::new()).is_err());
    }
}
