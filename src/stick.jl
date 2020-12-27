# Analyzing a wooden puzzle I have at home and working generating additional
# puzzles from it

# Each stick has up to 6 groves, 3 on each sides. I number these groves as
#
#  6 5 4
# ‾V‾‾‾V‾
# _Λ_Λ___
#  3 2 1
# 
# (U+203E : Overline, U+039B / U+03BB: Lambda)
#
# And then can compactly encode each stick as binary number. This last stick is
# 0b101110 = 46. Since there are some rotations we can do, this same stick can
# be represented by 29, 43, 46 or 63. I take the lowest number (29) to be the
# canonical representation of the stick.

using JuMP, GLPK

function notch_list(repr::Int)::Vector{Int}
    d = digits(repr, base=2, pad=6)
    @assert length(d) == 6 "The integer representation $repr is not well formed."
    d
end

function orient_notch_list(ls, orientation)
    if orientation == 1
        ls
    elseif orientation == 2
        [ls[3], ls[2], ls[1], ls[6], ls[5], ls[4]]
    elseif orientation == 3
        [ls[4], ls[5], ls[6], ls[1], ls[2], ls[3]]
    else
        [ls[6], ls[5], ls[4], ls[3], ls[2], ls[1]]
    end
end

draw_top_notch(isNotch::Int) = isNotch == 1 ? "V" : "‾"
draw_bot_notch(isNotch::Int) = isNotch == 1 ? "Λ" : "_"

"""Use println(draw_stick(29)) to draw a single stick to the console."""
function draw_stick(repr::Int; orientation=1)::String
    d = orient_notch_list(notch_list(repr), orientation)
    """‾$(draw_top_notch(d[6]))‾$(draw_top_notch(d[5]))‾$(draw_top_notch(d[4]))‾
    _$(draw_bot_notch(d[3]))_$(draw_bot_notch(d[2]))_$(draw_bot_notch(d[1]))_"""
end

notch_count(repr::Int)::Int = count_ones(repr)

# List of all the sticks that are possible.
# Note that sticks 0, 1, 2, 3, 5, 7 are terminal.
canonical_sticks = [0, 1, 2, 3, 5, 7, 9, 10, 11, 12, 13, 14, 15, 18, 19, 21, 23, 27, 29, 30, 31, 45, 47, 63]
@assert length(canonical_sticks) == 24

"""Check for horizontal symmetry (i.e. up stays up)"""
function is_h_symmetric(repr::Int)::Bool
    d = notch_list(repr)
    d[1] == d[3] && d[4] == d[6]
end

"""Check for vertical symmetry (i.e. up becomes down)"""
function is_v_symmetric(repr::Int)::Bool
    d = notch_list(repr)
    d[1] == d[4] && d[2] == d[5] && d[3] == d[6]
end

"""Check for rotational symmetry. Note that having any two symmetries implies the third one."""
function is_hv_symmetric(repr::Int)::Bool
    d = notch_list(repr)
    d[1] == d[6] && d[2] == d[5] && d[3] == d[4]
end

@assert is_h_symmetric(45)
@assert is_h_symmetric(21)
@assert !is_h_symmetric(9)

@assert is_v_symmetric(45)
@assert !is_v_symmetric(21)
@assert is_v_symmetric(9)

function reorient_index(orientation::Int, index::Int)::Int
    if orientation == 1
        index
    elseif orientation == 2 # h flip
        Dict(1 => 3, 2 => 2, 3 => 1, 4 => 6, 5 => 5, 6 => 4)[index]
    elseif orientation == 3 # v flip
        Dict(1 => 4, 2 => 5, 3 => 6, 4 => 1, 5 => 2, 6 => 3)[index]
    else # hv flip
        Dict(1 => 6, 2 => 5, 3 => 4, 4 => 3, 5 => 2, 6 => 1)[index]
    end
    end

function notch_at(repr::Int, orientation::Int, index::Int)::Int
    notch_list(repr)[reorient_index(orientation, index)]
end

@assert notch_at(2, 1, 1) == 0
@assert notch_at(23, 3, 6) == 1
@assert notch_at(12, 2, 1) == 1
@assert notch_at(11, 4, 6) == 1

# Here is a simple example I worked out. The marbles in the bottom form the shape
# 
# V V ‾ | 1 2 3 | Here each marble is a ‾, as it works as a not-grove.
# V ‾ V | 4 5 6 | Meaning this setup has the representation 0b010101011 = 171
# ‾ V ‾ | 7 8 9 | where representations range from 0 to 511 (inclusive).
# 
# On this we will stack two layers, made out of [ 1, 2, 7, 10, 13, 13 ] where the
# 13 is included twice. But we'll place it in two different orientations.


marbles_repr = 171
marbles = digits(marbles_repr, base=2, pad=9)
@assert marbles == [1, 1, 0, 1, 0, 1, 0, 1, 0]

sticks = [1, 2, 7, 10, 13]
stick_count = [1, 1, 1, 1, 2]
layers = 2
@assert length(sticks) == length(stick_count)
@assert sum(stick_count) >= 3 * layers


# Setting up a model to optimize
m = Model(GLPK.Optimizer)

# Variable name is (stick)(position)(orientation=[0, h, v, hv])
@variable(m, spo[1:length(sticks), 1:6, 1:4], Bin)

# for all symmetric sticks, force the symmetry partners to be zero.
for i in 1:length(sticks)
    if is_h_symmetric(sticks[i])
        if is_v_symmetric(sticks[i])
            # Fully symmetric, set all but one orientation to 0
            @constraint(m, spo[i, 1:end, 2:end] .== 0)
        else
            # Only h symmetric, but not v symmetric. This means we eliminate
            # orientations 2 and 4.
            @constraint(m, spo[i, 1:end, 2] .== 0)
            @constraint(m, spo[i, 1:end, 4] .== 0)
        end
    elseif is_v_symmetric(sticks[i])
        # Only v symmetric, but not h symmetric. We eliminate orientations
        # 3 and 4.
        @constraint(m, spo[i, 1:end, 3] .== 0)
        @constraint(m, spo[i, 1:end, 4] .== 0)
    elseif is_hv_symmetric(sticks[i])
        # Only rotation symmetric, not mirror symmetric. We still eliminate
        # 3 and 4 but now they are paired differently than before.
        @constraint(m, spo[i, 1:end, 3] .== 0)
        @constraint(m, spo[i, 1:end, 4] .== 0)
    end
    end

# Constrain that every stick is only used at most `count` times.
@constraint(m, sum(spo, dims=(2, 3)) .<= stick_count )

# Constraint that every position contains at most one stick.
@constraint(m, sum(spo, dims=(1, 3)) .<= 1)

# The objective is to place as many sticks as possible.
@objective(m, Max, sum(spo))

# Now we need add the condition for sticks properly sitting on each other.
# This condition depends on the actual sticks that are in the mix and is quite
# heterogeneous.
# We'll also need an initial and terminal condition.

# sum over all sticks and all orientations, filter by "Has a notch".
function notch_sum(sticks, spo, notch_index, position)
    sum(notch_at.(sticks, transpose(1:4), notch_index) .* spo[1:end, position, 1:4])
end

# Initial layer: Marbles + first layer.

# Positions that are "at the bottom of" the touchpoints.
bottom_positions = nothing
# Positions that are "on top of" the touchpoints.
top_positions = collect(1:3)

@constraint(m, marbles[1] + notch_sum(sticks, spo, 1, top_positions[1]) == 1)
@constraint(m, marbles[2] + notch_sum(sticks, spo, 2, top_positions[1]) == 1)
@constraint(m, marbles[3] + notch_sum(sticks, spo, 3, top_positions[1]) == 1)
@constraint(m, marbles[4] + notch_sum(sticks, spo, 1, top_positions[2]) == 1)
@constraint(m, marbles[5] + notch_sum(sticks, spo, 2, top_positions[2]) == 1)
@constraint(m, marbles[6] + notch_sum(sticks, spo, 3, top_positions[2]) == 1)
@constraint(m, marbles[7] + notch_sum(sticks, spo, 1, top_positions[3]) == 1)
@constraint(m, marbles[8] + notch_sum(sticks, spo, 2, top_positions[3]) == 1)
@constraint(m, marbles[9] + notch_sum(sticks, spo, 3, top_positions[3]) == 1)

# Layer 2: first layer + second layer

bottom_positions = collect(1:3)
top_positions = collect(4:6)

@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[1]) + notch_sum(sticks, spo, 1, top_positions[1]) == 1)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[1]) + notch_sum(sticks, spo, 1, top_positions[2]) == 1)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[1]) + notch_sum(sticks, spo, 1, top_positions[3]) == 1)
@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[2]) + notch_sum(sticks, spo, 2, top_positions[1]) == 1)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[2]) + notch_sum(sticks, spo, 2, top_positions[2]) == 1)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[2]) + notch_sum(sticks, spo, 2, top_positions[3]) == 1)
@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[3]) + notch_sum(sticks, spo, 3, top_positions[1]) == 1)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[3]) + notch_sum(sticks, spo, 3, top_positions[2]) == 1)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[3]) + notch_sum(sticks, spo, 3, top_positions[3]) == 1)

# Layer 3: last layer must be smooth at the top.

bottom_positions = collect(4:6)
top_positions = nothing

@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[1]) == 0)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[1]) == 0)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[1]) == 0)
@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[2]) == 0)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[2]) == 0)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[2]) == 0)
@constraint(m, notch_sum(sticks, spo, 4, bottom_positions[3]) == 0)
@constraint(m, notch_sum(sticks, spo, 5, bottom_positions[3]) == 0)
@constraint(m, notch_sum(sticks, spo, 6, bottom_positions[3]) == 0)

# Optimizing the model.
optimize!(m)
objective_value(m)


values = value.(spo)
for p in 1:6
    s, o = Tuple(argmax(values[1:end, p, 1:4]))
    println(draw_stick(sticks[s]; orientation=o))
end