use super::*;

pub trait ProximityTestingMode: 'static + Clone + Copy + std::fmt::Debug + PartialEq + Eq {
    fn num_queries_for_rate_and_bits_of_security(
        &self,
        security_bits: u32,
        neg_rate_log_2: u32,
    ) -> u32;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct UniqueDecodingMode;

impl ProximityTestingMode for UniqueDecodingMode {
    fn num_queries_for_rate_and_bits_of_security(
        &self,
        security_bits: u32,
        neg_rate_log_2: u32,
    ) -> u32 {
        // maximum distance delta = (1-rate)/2
        // soundless error is (1 - delta)^num_queries (simplified for now)

        let delta = (1f64 - (1f64 / 2f64.powi(neg_rate_log_2 as i32))) / 2f64;
        assert!(delta < 1f64);
        let one_minus_delta = 1f64 - delta;
        let bits_per_query = one_minus_delta.log2() * -1f64;
        let num_queries = (security_bits as f64) / bits_per_query;

        num_queries.ceil() as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PessimisticConjectureMode;

impl ProximityTestingMode for PessimisticConjectureMode {
    fn num_queries_for_rate_and_bits_of_security(
        &self,
        security_bits: u32,
        neg_rate_log_2: u32,
    ) -> u32 {
        // Even though the conjecture doesn't hold, the correction terms are O(1/q) and O(1/log(q)),
        // and for ~31 bit field those yeild in 10% more queries. So we do extra 20% more queries to have a margin.

        let bits_per_query = neg_rate_log_2;
        let num_queries = security_bits / bits_per_query;

        (num_queries * 120).div_ceil(100) as u32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct JohnsonBoundMode;

impl ProximityTestingMode for JohnsonBoundMode {
    fn num_queries_for_rate_and_bits_of_security(
        &self,
        security_bits: u32,
        neg_rate_log_2: u32,
    ) -> u32 {
        // maximum distance delta = 1-sqrt(rate)

        let delta = 1f64 - f64::sqrt(1f64 / 2f64.powi(neg_rate_log_2 as i32));
        assert!(delta < 1f64);
        let one_minus_delta = 1f64 - delta;
        let bits_per_query = one_minus_delta.log2() * -1f64;
        let num_queries = (security_bits as f64) / bits_per_query;

        num_queries.ceil() as u32
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn compute_for_udr() {
        let mode = UniqueDecodingMode;
        let num_queries = mode.num_queries_for_rate_and_bits_of_security(128, 1);
        dbg!(num_queries);
    }

    #[test]
    fn compute_for_conjecture() {
        let mode = PessimisticConjectureMode;
        let num_queries = mode.num_queries_for_rate_and_bits_of_security(128, 1);
        dbg!(num_queries);
    }

    #[test]
    fn compute_for_johnson_bound() {
        let mode = JohnsonBoundMode;
        let num_queries = mode.num_queries_for_rate_and_bits_of_security(128, 1);
        dbg!(num_queries);
    }
}
