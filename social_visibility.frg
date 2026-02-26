#lang forge/froglet

abstract sig Boolean {}
one sig True, False extends Boolean {}

// 朋友圈可见度：公开、仅好友、指定好友、私密
abstract sig Visibility {}
one sig Public, FriendsOnly, SpecificFriends, Private extends Visibility {}

sig User {
    // 好友关系
    friends: pfunc User -> Boolean,
    // 黑名单关系
    blocked: pfunc User -> Boolean,
    
    // 账号全局开关
    stranger_see_recent: one Boolean,  // 允许陌生人看十条
    moments_closed: one Boolean,       // 一键关闭/停用朋友圈
    limit_recent_10: one Boolean       // 仅向好友展示最近十条
}

sig Post {
    author: one User,
    visibility: one Visibility,
    allowed_viewers: pfunc User -> Boolean,
    timestamp: one Int
}

-- 约束条件

pred wellformed {
    all u: User | u.friends[u] != True // 不能是自己的好友
    all u1, u2: User | u2.friends[u1] = True implies u1.friends[u2] = True // 好友关系对称
    
    // 黑名单的逻辑约束
    all u: User | u.blocked[u] != True // 不能把自己拉黑
    all u1, u2: User | u1.blocked[u2] = True implies u1.friends[u2] != True // 拉黑后自动解除好友关系（或不允许同时是好友又是黑名单）
    
    all p: Post | p.timestamp >= 0 // 时间戳非负
    all disj p1, p2: Post | (p1.author = p2.author) implies p1.timestamp != p2.timestamp // 同一作者的帖子时间戳不同
    
    // 朋友圈可见度和 allowed_viewers 的约束：
    all p: Post, u: User | (p.visibility = SpecificFriends and p.allowed_viewers[u] = True) implies p.author.friends[u] = True
    all p: Post, u: User | p.visibility != SpecificFriends implies p.allowed_viewers[u] != True
}

-- 核心逻辑：谁到底能看

pred isRecent[p: Post] {
    // 是否算“最近十条”
    #{other_p: Post | other_p.author = p.author and other_p.timestamp > p.timestamp} < 10
}

pred canSee[viewer: User, p: Post] {
    // 是不是作者本人？自己永远能看自己的帖子
    viewer = p.author 
    or 
    (
        // 如果不是作者本人，必须经过全局开关的毒打
        viewer != p.author 
        
        // 黑名单的一票否决：如果查看者在作者的黑名单里，绝对看不了
        and p.author.blocked[viewer] != True
        
        // 作者是不是一键关闭了朋友圈？（一票否决）
        and p.author.moments_closed = False 
        
        // 如果作者没有开启“仅展示最近十条”，那就不受时间戳限制；如果开启了，就只能看最近十条
        and (p.author.limit_recent_10 = False or isRecent[p]) 
        
        // 帖子本身的独立权限
        and 
        (
            // 好友视角的独立权限判断
            (
                p.author.friends[viewer] = True and ( 
                    p.visibility = Public 
                    or p.visibility = FriendsOnly 
                    or (p.visibility = SpecificFriends and p.allowed_viewers[viewer] = True) 
                )
            )
            or 
            // 陌生人视角的独立权限判断
            (
                p.author.friends[viewer] != True and ( 
                    p.visibility = Public 
                    and p.author.stranger_see_recent = True 
                    and isRecent[p] // 陌生人本来就有10条限制
                )
            )
        )
    )
}

-- 场景测试

pred known_scenario {
    some disj Alice, Bob, Charlie: User |
    some disj p_pub, p_priv, p_spec: Post | {
        
        // 人物关系设定
        Bob.friends[Alice] = True
        Alice.friends[Bob] = True
        all u: User | Charlie.friends[u] != True
        
        // 【新增】Alice 把某个无辜路人拉黑了
        // 假设系统里有第四个人 Dave，Alice 拉黑了他
        
        // Alice 的全局开关设定
        Alice.stranger_see_recent = True
        Alice.moments_closed = False     
        Alice.limit_recent_10 = True     

        // 三条帖子测试一下
        p_pub.author = Alice and p_pub.visibility = Public and p_pub.timestamp = 10
        p_priv.author = Alice and p_priv.visibility = Private and p_priv.timestamp = 9
        p_spec.author = Alice and p_spec.visibility = SpecificFriends and p_spec.allowed_viewers[Bob] = True and p_spec.timestamp = 8

        canSee[Bob, p_pub]          
        not canSee[Bob, p_priv]    
        canSee[Bob, p_spec]         
        
        canSee[Charlie, p_pub]      
        not canSee[Charlie, p_priv] 
        not canSee[Charlie, p_spec] 
    }
}

run {
    wellformed
    known_scenario
} for 5 Int, exactly 3 User, exactly 3 Post