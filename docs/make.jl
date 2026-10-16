using Documenter, MaterialDocs
using GruntzLimit

DocMeta.setdocmeta!(GruntzLimit, :DocTestSetup, :(using GruntzLimit); recursive = true)

makedocs(
    sitename = "GruntzLimit.jl",
    modules = [GruntzLimit],
    checkdocs = :exports,
    format = Material3(theme = :default, dark_mode = :toggle, prettyurls = get(ENV, "CI", nothing) == "true", edit_link = "main"),
    pages = [
        "Home" => "index.md",
        "Usage" => "usage.md",
        "How it works" => "algorithm.md",
        "Reference" => "reference.md",
    ],
)

deploydocs(repo = "github.com/jverzani/GruntzLimit.jl.git", devbranch = "main", push_preview = true)
