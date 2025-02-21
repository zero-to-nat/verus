include "../shared/AbstractSpec.t.dfy"

module ClientSpec refines AbstractSpec {
    datatype Event = SendRequest | ReceiveResponse

    datatype Constants = Constants

    datatype Variables = Variables(nums: seq<(int, int)>, sum: seq<int>)

    ghost predicate Init(c: Constants, v: Variables) {
        && |v.nums| == 0
        && |v.sum| == 0
    }

    ghost predicate SendRequest(c: Constants, v: Variables, v': Variables) {
        && |v'.nums| == |v.nums| + 1
        && v'.nums[..|v'.nums| - 1] == v.nums
        && v.sum == v'.sum
    }

    ghost predicate ReceiveResponse(c: Constants, v: Variables, v': Variables) {
        && v.nums == v'.nums
        && |v.sum| < |v.nums|
        && |v'.sum| == |v.sum| + 1
        && v'.sum[..|v'.sum| - 1] == v.sum
        && v'.sum[|v'.sum| - 1] == v.nums[|v'.sum| - 1].0 + v.nums[|v'.sum| - 1].1
    }

    ghost predicate Next(c: Constants, v: Variables, v': Variables, evt: Event) {
        match evt {
            case SendRequest => SendRequest(c, v, v')
            case ReceiveResponse => ReceiveResponse(c, v, v')
        }
    }
}