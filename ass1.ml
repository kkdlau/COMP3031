(* Lau, Ka Kit Danny, kkdlau, 20650186 *)

datatype flight = F of int * int;
datatype flights = Fs of flight list;

fun first (x, _) = x;
fun second (_, y) = y;

(* Q2 *)
fun flight_dist(F f) = #2f;

fun flatten([]) = [] | flatten(list) = flight_dist(hd list)::flatten(tl list);

fun create_list(size) = if size = 0 then [] else 0::create_list(size - 1);

fun max(v, []) = v | max(v, l) = if v > hd(l) then max(v, tl l) else max(hd l, tl l);

fun increment_element(list, index) = if index = 1 then (hd(list) + 1)::tl(list) else hd(list)::increment_element(tl list, index - 1);

fun occurrence_counting(counting_list, []) = counting_list | 
occurrence_counting(counting_list, list_to_count) = occurrence_counting(increment_element(counting_list, (hd list_to_count) + 1), tl list_to_count);

fun append_index_if_meet_max(intial, max, [], count) = intial |
append_index_if_meet_max(intial, max, occur_list, count) = 
    if hd occur_list = max then
        append_index_if_meet_max(intial @ [count - 1], max, tl occur_list, count + 1)
    else
        append_index_if_meet_max(intial, max, tl occur_list, count + 1)
    ;

fun popular_cities(Fs []) = [] | 
popular_cities (Fs list) = 
    let 
        val flat_list = flatten(list)
        val max_in_list = max(hd flat_list, tl flat_list)
        val occur_list_empty = create_list(max_in_list + 1)
        val occur_list = occurrence_counting(occur_list_empty, flat_list)
        val max_occurrence = max(hd occur_list, tl occur_list)
        val result = append_index_if_meet_max([], max_occurrence, occur_list, 1)
    in
        result
    end;

(* Q3 *)

fun f_as_list(F(x, y)) = [x, y];

fun flatten2([]) = [] | flatten2(list) = f_as_list(hd list)@flatten2(tl list);

fun from(F(x, y)) = x;

fun endCity(F(x, y)) = y;

fun length([]) = 0 | length(list) = 1 + length(tl list);

fun set_visited(visited, v) = increment_element(visited, v + 1);

fun get_by_index(list, index) = if index + 1 = 1 then hd list else get_by_index(tl list, index - 1);

fun adj(Fs [], visited, f) = [] | adj(Fs paths, visited, f) = 
    if from(hd paths) = f andalso get_by_index(visited, endCity(hd paths)) = 0 then
        (hd paths)::adj(Fs(tl paths), visited, f)
    else
        adj(Fs(tl paths), visited, f);

fun sum([]) = 0 | sum(h::t) = h + sum(t);

fun foreach(funcs, []) = [] | foreach(funcs, h::t) = funcs(h)::foreach(funcs, t);

fun DFS(Fs paths, visited, to_visit, end_pos) = 
let 
    val visited = set_visited(visited, to_visit)
    val adj_list = adj(Fs(paths), visited, to_visit)
in 
    if end_pos = to_visit then
        1
    else
        if length(adj_list) = 0 then
            0
        else
            sum(foreach((fn (adj_memebr) => DFS(Fs(paths), visited, endCity adj_memebr, end_pos)), adj_list))
end;

fun count_paths(Fs [], f) = 0 | count_paths(Fs paths, f) = 
let
    val visited_initial = create_list(max(0, flatten2(paths)) + 1)
    val visited = set_visited(visited_initial, first f)
in
    DFS(Fs paths, visited, first f, second f)
end;

(* Q4 *)

fun dequeue([]) = (nil, []) | dequeue(h::t) = (h, t);

fun append_queue([], e) = [e] | append_queue(list, e) = list @ [e];

fun BFS_adj(Fs [], visited, f, prefix) = [] | BFS_adj(Fs paths, visited, f, prefix) = 
    if from(hd paths) = f andalso get_by_index(visited, endCity(hd paths)) = 0 then
        (append_queue(prefix, endCity(hd paths)))::BFS_adj(Fs(tl paths), visited, f, prefix)
    else
        BFS_adj(Fs(tl paths), visited, f, prefix);

fun last([]) = ~1 | last(list) = List.last(list);

fun BFS(Fs paths, visited, queue, end_city): int list list = 
    if length queue = 0 then
        []
    else let
        val (v, queue_update) = dequeue(queue)
    in
        if (last v) = end_city then
            v :: BFS(Fs paths, visited, queue_update, end_city)
        else let 
            val visited_update = set_visited(visited, last v)
            val adj_list = BFS_adj(Fs paths, visited_update, last v, v)
            val joined = queue_update @ adj_list
        in
            BFS(Fs paths, visited_update, joined, end_city)
        end
    end;

fun shortest_paths(Fs [], f) = [] | shortest_paths(Fs paths, f) = 
let 
    val visited_initial = create_list(max(0, flatten2(paths)) + 1)
in
    let
        val possible_paths = BFS(Fs paths, visited_initial, [[0]], second f)
    in
        if length possible_paths = 0 then []
        else List.filter (fn (path) => length path = length(hd possible_paths)) possible_paths
    end
end;

(* Q1 *)
fun reachable(Fs [], f) = false | reachable(Fs paths, f) = count_paths(Fs paths, f) > 0;

(* Q5 *)

fun enumerate_possible_pairs(i, j, max_i, max_j): (int * int) list =
    if i = max_i andalso j = max_j then
        [(i, j)]
    else if i >= max_i then
        (i, j)::enumerate_possible_pairs(0, j + 1, max_i, max_j)
    else 
        (i, j)::enumerate_possible_pairs(i + 1, j, max_i, max_j);

fun reachable_within(Fs [], f, path_length) = false | reachable_within(Fs paths, f, path_length) = 
let
    val possible_paths = shortest_paths(Fs paths, f)
in
    if length possible_paths = 0 then
        false
    else if length(hd possible_paths) > path_length + 1 then
        false
    else
        true
end;

fun search_cities(Fs [], path_length: int): (int * int) list = [] |
search_cities(Fs paths, path_length: int) = 
let
    val all_cities = flatten2(paths)
    val max_num_city = max(0, all_cities)
    val pairs = List.filter (fn (pair) => (first pair) <> (second pair)) (enumerate_possible_pairs(0, 0, max_num_city, max_num_city));
in
    List.filter (fn (pair) => reachable_within(Fs paths, pair, path_length)) pairs
end;