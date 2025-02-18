module Types {
    datatype Option<T> = Some(value:T) | None

    type SeqNo = nat

    datatype ServiceRequest<T> = ServiceRequest(seqNo: SeqNo, val: T)
    datatype ServiceResponse<T> = ServiceResponse(seqNo: SeqNo, val: T)
}