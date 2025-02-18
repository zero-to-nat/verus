include "ClientSpec.t.dfy"
include "../shared/Network.t.dfy"

module ClientNetwork refines AbstractNetwork {
    datatype Message = ClientRequest(request: ServiceRequest<(int, int)>) | ClientResponse(response: ServiceResponse<int>)
}