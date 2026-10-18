module GruntzLimit

include("Gruntz.jl")
using .Gruntz
using .Gruntz: LimitCases, CaseCondition    # public types, not exported
export gruntz_limit, gruntz_cases, GruntzError


end
