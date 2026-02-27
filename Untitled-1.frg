#lang forge

option run_sterling "vis.js"

/* * 动态社交媒体可见性模型 (Dynamic Social Media Visibility Model)
 * 这是一个包含状态流转 (State Transitions) 的高级模型。
 * 它模拟了用户之间关系的演变（加好友、拉黑），并验证了在这些动作发生前后，
 * 帖子可见性权限的严密性。
 */

abstract sig Visibility {}
one sig Public, FriendsOnly, SpecificFriends, ExcludeFriends, Private extends Visibility {}

-- 静态实体：User 和 Post 本身在系统中一直存在
sig User {}

sig Post {
    author: one User,
    visibility: one Visibility,
    timestamp: one Int
}

-- 动态实体：State 保存了系统中所有会随时间发生变化的属性
sig State {
    friends: set User -> User,          -- 好友关系映射
    blocked: set User -> User,          -- 拉黑映射 (u1 -> u2 表示 u1 拉黑了 u2)
    muted: set User -> User,            -- 屏蔽映射 (u1 -> u2 表示 u1 屏蔽了 u2 的动态)
    
    -- 账户全局设置
    stranger_see_recent: set User,      -- 允许陌生人看最近十条的用户集合
    moments_closed: set User,           -- 关闭朋友圈的用户集合
    limit_recent_10: set User,          -- 仅展示最近十条的用户集合
    
    -- 帖子颗粒度权限
    allowed_viewers: set Post -> User,  -- SpecificFriends 的白名单
    excluded_viewers: set Post -> User  -- ExcludeFriends 的黑名单
}

-- ------------------------------------------------------------------
-- 1. 约束与查询 (Constraints & Queries)
-- ------------------------------------------------------------------

-- 判断一个帖子是否是该作者的最近 10 条（这个规则是静态的，只依赖 Post）
pred isRecent[p: Post] {
    #{other_p: Post | other_p.author = p.author and other_p.timestamp > p.timestamp} < 10
}

-- 针对特定的状态 s，检查数据结构是否合法
pred wellformed[s: State] {
    -- 静态时间戳检查
    all p: Post | p.timestamp >= 0 
    all disj p1, p2: Post | (p1.author = p2.author) implies p1.timestamp != p2.timestamp 
    
    -- 基础关系约束
    no u: User | u in s.friends[u]  -- 不能加自己为好友
    no u: User | u in s.blocked[u]  -- 不能拉黑自己
    no u: User | u in s.muted[u]    -- 不能屏蔽自己
    
    all u1, u2: User | u1 in s.friends[u2] implies u2 in s.friends[u1] -- 好友是双向的
    all u1, u2: User | u2 in s.blocked[u1] implies u2 not in s.friends[u1] -- 拉黑后自动解除好友
    
    -- 帖子颗粒度权限逻辑约束
    all p: Post, u: User | (p.visibility = SpecificFriends and u in s.allowed_viewers[p]) implies u in s.friends[p.author]
    all p: Post, u: User | p.visibility != SpecificFriends implies u not in s.allowed_viewers[p]
    
    all p: Post, u: User | (p.visibility = ExcludeFriends and u in s.excluded_viewers[p]) implies u in s.friends[p.author]
    all p: Post, u: User | p.visibility != ExcludeFriends implies u not in s.excluded_viewers[p]
}

-- 核心权限逻辑：判断 viewer 在状态 s 下能否看到 p
pred canSee[viewer: User, p: Post, s: State] {
    viewer = p.author 
    or 
    (
        viewer != p.author 
        and viewer not in s.blocked[p.author]  -- 没有被作者拉黑
        and p.author not in s.muted[viewer]    -- 没有屏蔽作者
        and p.author not in s.moments_closed   -- 作者没有关闭朋友圈
        and (p.author not in s.limit_recent_10 or isRecent[p]) -- 时间限制
        
        and 
        (
            -- 好友视角逻辑
            (
                viewer in s.friends[p.author] and ( 
                    p.visibility = Public 
                    or p.visibility = FriendsOnly 
                    or (p.visibility = SpecificFriends and viewer in s.allowed_viewers[p]) 
                    or (p.visibility = ExcludeFriends and viewer not in s.excluded_viewers[p])
                )
            )
            or 
            -- 陌生人视角逻辑
            (
                viewer not in s.friends[p.author] and ( 
                    p.visibility = Public 
                    and p.author in s.stranger_see_recent
                    and isRecent[p] 
                )
            )
        )
    )
}

-- ------------------------------------------------------------------
-- 2. 动作流转 (State Transitions / Actions)
-- ------------------------------------------------------------------

-- 初始状态设定
pred init[s: State] {
    wellformed[s]
    no s.friends
    no s.blocked
    no s.muted
}

-- 动作：u1 添加 u2 为好友
pred do_add_friend[pre: State, post: State, u1, u2: User] {
    wellformed[pre]
    wellformed[post]
    
    -- 前置条件：不是自己，当前不是好友，且没有互相拉黑
    u1 != u2
    u2 not in pre.friends[u1]
    u2 not in pre.blocked[u1]
    u1 not in pre.blocked[u2]
    
    -- 状态更新：加上双向好友关系
    post.friends = pre.friends + (u1 -> u2) + (u2 -> u1)
    
    -- 帧约束 (Frame conditions)：其他状态必须保持不变
    post.blocked = pre.blocked
    post.muted = pre.muted
    post.stranger_see_recent = pre.stranger_see_recent
    post.moments_closed = pre.moments_closed
    post.limit_recent_10 = pre.limit_recent_10
    post.allowed_viewers = pre.allowed_viewers
    post.excluded_viewers = pre.excluded_viewers
}

-- 动作：u1 拉黑 u2
pred do_block[pre: State, post: State, u1, u2: User] {
    wellformed[pre]
    wellformed[post]
    
    -- 前置条件：不是自己，且还没有拉黑
    u1 != u2
    u2 not in pre.blocked[u1]
    
    -- 状态更新：加入黑名单，并强制解除双向好友关系
    post.blocked = pre.blocked + (u1 -> u2)
    post.friends = pre.friends - (u1 -> u2) - (u2 -> u1)
    
    -- 帧约束
    post.muted = pre.muted
    post.stranger_see_recent = pre.stranger_see_recent
    post.moments_closed = pre.moments_closed
    post.limit_recent_10 = pre.limit_recent_10
    post.allowed_viewers = pre.allowed_viewers
    post.excluded_viewers = pre.excluded_viewers
}

-- 定义一个完整的事件流 (Trace)
pred trace {
    some s_init, s_mid, s_final: State | {
        some Alice, Bob: User | {
            Alice != Bob
            
            -- 第一阶段：系统初始状态
            init[s_init]
            Alice not in s_init.stranger_see_recent  -- Alice 不允许陌生人看
            
            -- 第二阶段：Alice 和 Bob 成为好友
            do_add_friend[s_init, s_mid, Alice, Bob]
            
            -- 第三阶段：Alice 突然拉黑了 Bob
            do_block[s_mid, s_final, Alice, Bob]
            
            -- 观察期：拿 Alice 的一条公开帖子来看看 Bob 在不同阶段的权限变化
            some p: Post | {
                p.author = Alice
                p.visibility = Public
                
                -- 状态1: 陌生人阶段 (看不到，因为没开 stranger_see_recent)
                not canSee[Bob, p, s_init]
                
                -- 状态2: 好友阶段 (能看到了)
                canSee[Bob, p, s_mid]
                
                -- 状态3: 拉黑阶段 (又看不到了，因为被拉黑且好友关系被强制解除了)
                not canSee[Bob, p, s_final]
            }
        }
    }
}

-- 运行该轨迹生成一个可视化实例
run { trace } for exactly 3 State, exactly 2 User, exactly 1 Post, 5 Int


-- ------------------------------------------------------------------
-- 3. 动态验证套件 (Verification & Assertions)
-- ------------------------------------------------------------------

test suite for canSee {   -- 👈 这里改成了真实存在的谓词 canSee
    test expect {
        -- 确保我们编写的 trace 是有解的（SAT），证明我们的逻辑行得通
        trace_is_valid: { trace } for exactly 3 State, exactly 2 User, exactly 1 Post, 5 Int is sat
        
        -- 【高光时刻：动态属性验证】
        -- 断言：如果你拉黑了某人，在下一个状态里，他绝对无法看到你的任何帖子！
        block_always_hides_posts: {
            some pre, post: State, u1, u2: User, p: Post | {
                -- 如果在 pre 到 post 之间，u1 拉黑了 u2
                do_block[pre, post, u1, u2]
                
                -- 并且 p 是 u1 的帖子
                p.author = u1
                
                -- 在 post 状态下，如果 u2 依然能看到 p，这就是个反例 (Bug)！
                canSee[u2, p, post]
            }
        } for exactly 2 State, 4 User, 4 Post, 5 Int is unsat 
    }
}