"use strict";

/* ============ 1. 符号集与属性矩阵 ============ */
const TIANGAN = ["甲","乙","丙","丁","戊","己","庚","辛","壬","癸"];
const DIZHI   = ["子","丑","寅","卯","辰","巳","午","未","申","酉","戌","亥"];

const WU_XING = {
  "甲":"木","乙":"木","丙":"火","丁":"火","戊":"土","己":"土",
  "庚":"金","辛":"金","壬":"水","癸":"水",
  "寅":"木","卯":"木","巳":"火","午":"火","申":"金","酉":"金",
  "亥":"水","子":"水","辰":"土","戌":"土","丑":"土","未":"土"
};
const YIN_YANG = {
  "甲":"阳","丙":"阳","戊":"阳","庚":"阳","壬":"阳",
  "寅":"阳","辰":"阳","午":"阳","申":"阳","戌":"阳","子":"阳",
  "乙":"阴","丁":"阴","己":"阴","辛":"阴","癸":"阴",
  "卯":"阴","巳":"阴","未":"阴","酉":"阴","亥":"阴","丑":"阴"
};

const SHISHEN_MAP = {
  "同|同":"比肩","同|异":"劫财",
  "生我|同":"偏印","生我|异":"正印",
  "我生|同":"食神","我生|异":"伤官",
  "克我|同":"七杀","克我|异":"正官",
  "我克|同":"偏财","我克|异":"正财"
};

const PROVINCE_FALLBACK_LNG = {
  "北京市":116.40,"上海市":121.47,"天津市":117.20,"重庆市":106.54,
  "河北省":114.48,"山西省":112.53,"辽宁省":123.38,"吉林省":125.35,
  "黑龙江省":126.63,"江苏省":118.78,"浙江省":120.15,"安徽省":117.27,
  "福建省":119.30,"江西省":115.89,"山东省":117.00,"河南省":113.65,
  "湖北省":114.31,"湖南省":112.98,"广东省":113.26,"海南省":110.35,
  "四川省":104.06,"贵州省":106.71,"云南省":102.73,"陕西省":108.95,
  "甘肃省":103.73,"青海省":101.74,"台湾省":121.50,
  "内蒙古自治区":111.65,"广西壮族自治区":108.33,"西藏自治区":91.11,
  "宁夏回族自治区":106.27,"新疆维吾尔自治区":87.68
};

/* ============ 2. 基础算子（严格对齐 Python 语义） ============ */
// Python 风格的向下取整除法 //
const floordiv = (a, b) => Math.floor(a / b);
// Python 风格的取模（结果恒为非负）%
const pymod = (a, n) => ((a % n) + n) % n;

function is_valid_date(year, month, day) {
  if (month < 1 || month > 12 || day < 1) return false;
  const astronomical_year = year > 0 ? year : year + 1;
  let is_leap;
  if (astronomical_year < 1582) {
    is_leap = (astronomical_year % 4 === 0);
  } else {
    is_leap = (astronomical_year % 4 === 0 && astronomical_year % 100 !== 0)
      || (astronomical_year % 400 === 0);
  }
  const days_in_month = [31, is_leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
  if (year === 1582 && month === 10 && day >= 5 && day <= 14) return false;
  return day <= days_in_month[month - 1];
}

function date_to_julian_day(year, month, day, hour, minute) {
  if (year < 0) year = year + 1;
  if (month <= 2) { year -= 1; month += 12; }
  let B;
  if ((year > 1582) || (year === 1582 && month > 10) || (year === 1582 && month === 10 && day >= 15)) {
    const A = floordiv(year, 100);
    B = 2 - A + floordiv(A, 4);
  } else {
    B = 0;
  }
  let jd = Math.floor(365.25 * (year + 4716)) + Math.floor(30.6001 * (month + 1)) + day + B - 1524.5;
  jd += (hour + minute / 60.0) / 24.0;
  return jd;
}

function get_shishen_relation(me, other) {
  const me_x = WU_XING[me], me_y = YIN_YANG[me];
  const ot_x = WU_XING[other], ot_y = YIN_YANG[other];
  const elements = ["木","火","土","金","水"];
  const dist = pymod(elements.indexOf(ot_x) - elements.indexOf(me_x), 5);
  const relation_map = { 0:"同", 1:"我生", 2:"我克", 3:"克我", 4:"生我" };
  const relation = relation_map[dist];
  const same = (me_y === ot_y) ? "同" : "异";
  return SHISHEN_MAP[relation + "|" + same];
}

/* ============ 3. 格局详解数据 ============ */
const PATTERN_DETAILS = {
  "正财": {
    "名称":"正财格",
    "生克路径":"日主力量去驾驭月令的务实财富（我克者为财）。需要日主自身有根基，方能担财。",
    "性格双重拆解":"显性：做事极有条理，金钱观务实，重视风险控制；隐性：有时过于斤斤计较，缺乏冒险精神，容易错失以小博大的机会。",
    "事业天花板":"适合在成熟体制、金融机构、实业供应链中担任核心管理或财务统筹，走稳健晋升路线。",
    "核心用神解法":"若全盘克泄过多导致身弱，最喜【正印/比肩】运来生扶抗财；若身强财轻，则喜【食神】来引通聪慧，源源不断生财。"
  },
  "偏财": {
    "名称":"偏财格",
    "生克路径":"日主与月令财富磁场发生非线性的剧烈碰撞。属于众人之财、流动之财、大财。",
    "性格双重拆解":"显性：豪爽侠义，极具商业敏锐度，擅长资源整合与人际博弈；隐性：投机心理重，耐性不足，容易大起大落。",
    "事业天花板":"天然的创业者、职业投资人或高级商务开拓者。不适合死板的打卡工作，天花板取决于资源杠杆的大小。",
    "核心用神解法":"偏财格最怕比劫夺财，若盘中出现劫财，必须有【官杀】护财，或者【食伤】通关，方能守住富贵。"
  },
  "正官": {
    "名称":"正官格",
    "生克路径":"月令对日主实施规范化的正向约束（克我者为官）。这是一种天地正气，代表名誉与正统约束力。",
    "性格双重拆解":"显性：光明磊落，自律性极强，极具社会责任感与行政天赋；隐性：思想容易传统保守，过度在乎外界评价，面对打破常规的变革时显得优柔寡断。",
    "事业天花板":"公职体系、大型跨国企业的核心行政高管、法务合规统筹。能在现有的稳定规则框架内做到行业最高层。",
    "核心用神解法":"官星最怕【伤官】克害（伤官见官）。系统最优解是配以【正印】，形成'官印相生'，则权柄稳固，名利双收。"
  },
  "七杀": {
    "名称":"七杀格",
    "生克路径":"月令对日主实施同极性的猛烈攻伐。这是一把双刃剑，代表剧烈的外部危机、强烈破坏力与变革能量。",
    "性格双重拆解":"显性：杀伐果断，危机处理能力极强，具有不服输的斗志与逆境翻盘的狼性；隐性：疑心较重，带有攻击性，容易让自己长期处于高度紧绷的焦虑状态。",
    "事业天花板":"竞争极度激烈的行业破局者、军警执法高层、或高风险领域的总指挥。往往在一场危机或行业洗牌中一战成名。",
    "核心用神解法":"七杀必须有制化方能为我所用。最优解有两种：一是用【食神】从正面硬撼压制（食神制杀）；二是用【正印】从侧面感化吸收（杀印相生）。"
  },
  "正印": {
    "名称":"正印格",
    "生克路径":"月令能量源源不断地无私输入、生扶日主（生我者为印）。代表母亲、福报、学术信仰与全方位的保护伞。",
    "性格双重拆解":"显性：心地慈悲，求知欲极强，具有极高的包容力与奉献精神，天然得长辈器重；隐性：容易陷入空想，行动力偏弱，在残酷的商业竞争中显得过于天真和书生气。",
    "事业天花板":"高校教授、核心科研人员、文化出版巨头、或慈善医疗机构负责人。适合走依靠声誉、思想和专业壁垒的持久路线。",
    "核心用神解法":"印星太重容易让人懒散。系统最喜【财星】来适度克制（财星配印），以物欲激活行动力；但切忌贪财坏印。"
  },
  "偏印": {
    "名称":"偏印格（枭神格）",
    "生克路径":"月令对日主实施同极性的非对称输入。这是一种剑走偏锋的领悟力，代表冷门知识、特异直觉与孤独深邃的能量。",
    "性格双重拆解":"显性：直觉惊人，能一眼看穿事物的漏洞，多才多艺，在特定偏门领域具备宗师级天赋；隐性：性格孤僻敏感，不易信任他人，内心深处常有强烈的疏离感与虚无感。",
    "事业天花板":"顶级研发黑客、心理学专家、尖端科技开拓者、或者特立独行的艺术创作者。在别人看不懂的冷门蓝海赛道做到绝对垄断。",
    "核心用神解法":"偏印格最怕'枭神夺食'。系统极度渴望【偏财】来强势制约偏印，通关释放食神能量。"
  },
  "食神": {
    "名称":"食神格",
    "生克路径":"日主纯能量的自然流露与向外输出。由于极性相同，输出温和且带有福气，属于'福寿星'。",
    "性格双重拆解":"显性：心态宽和，才华内敛而不张扬，极为注重生活品质、审美与精神自由；隐性：有时流于随性，缺乏危机感，面对高强度的逼迫时容易选择躺平或逃避。",
    "事业天花板":"顶级产品架构师、文创策划巨头、高端美学、咨询顾问或技术专家。不需要去和别人惨烈撕咬，靠才华自然吸引提携。",
    "核心用神解法":"食神最喜【财星】顺势流转（食神生财），将才华彻底变现；同时最怕【偏印】暗中克制导致格局受损。"
  },
  "伤官": {
    "名称":"伤官格",
    "生克路径":"日主能量爆发式的、跨极性的强烈输出。这是最狂暴的才华与创造力，天生具有打破常规、颠覆旧体制的叛逆因子。",
    "性格双重拆解":"显性：才华横溢，口才极佳，领悟力惊人，极具创新精神与降维打击的个人魅力；隐性：恃才傲物，说话容易扎人，天生不服管束，容易招惹口舌是非、得罪权贵。",
    "事业天花板":"演艺界巨星、自由职业意见领袖、颠覆性科技项目的核心研发总监、或顶尖投资人。天花板高度取决于其才华被变现的程度。",
    "核心用神解法":"伤官必须驯服。上策是配以【正印】形成'伤官配印'，以理智约束狂气；下策是顺势配以【财星】（伤官生财），转化为红利。"
  },
  "比肩": {
    "名称":"建禄/月劫倾向（独立格）",
    "生克路径":"月令能量与日主完全同气、同质。整个天地磁场在充盈你的自我意识，属于极强的主观能动性之格。",
    "性格双重拆解":"显性：意志极其坚定，自信独立，凡事习惯亲力亲为，极具同业竞争的耐力与骨气；隐性：极为固执，很难听进别人的劝告，有时显得过于独断专行，多竞争分财。",
    "事业天花板":"独立创业者、合伙企业的核心技术领袖、或者竞技、销售等需要高频肉搏行业的金牌开拓者。拼的是纯粹的个人硬抗能力。",
    "核心用神解法":"满盘同气最容易导致比劫夺财。系统极度需要【官杀】作为高悬的威慑规管；或者配以【食伤】将狂暴力量引导输出。"
  },
  "劫财": {
    "名称":"建禄/月劫倾向（独立格）",
    "生克路径":"月令能量与日主完全同气、同质。整个天地磁场在充盈你的自我意识，属于极强的主观能动性之格。",
    "性格双重拆解":"显性：意志极其坚定，自信独立，凡事习惯亲力亲为，极具同业竞争的耐力与骨气；隐性：极为固执，很难听进别人的劝告，有时显得过于独断专行，多竞争分财。",
    "事业天花板":"独立创业者、合伙企业的核心技术领袖、或者竞技、销售等需要高频肉搏行业的金牌开拓者。拼的是纯粹的个人硬抗能力。",
    "核心用神解法":"满盘同气最容易导致比劫夺财。系统极度需要【官杀】作为高悬的威慑规管；或者配以【食伤】将狂暴力量引导输出。"
  }
};

const FALLBACK_DETAIL = {
  "名称":"特殊/均衡格",
  "生克路径":"全盘五行力量处于多极平衡状态，未形成单一绝对统治力的能量场。",
  "性格双重拆解":"显性：处事圆融，极具大局观，能在不同派系间游刃有余；隐性：有时缺乏鲜明的个人核心标签，容易陷入多头拉扯的内耗。",
  "事业天花板":"大型复杂跨国项目的高级统筹者、多方利益博弈的调解人或综合性高管。",
  "核心用神解法":"此格不求单点突破，最喜大运走【五行流通】之运，能量不断流则一生安稳，富贵自来。"
};

/* ============ 4. 核心排盘引擎 ============ */
function execute_global_fortune_engine(year, month, day, hour, minute, longitude, time_type) {
  let t_year = year, t_month = month, t_day = day, t_hour = hour, t_min = minute;

  if (time_type === 1) {
    const lng_offset = (longitude - 120.0) * 4;
    const astronomical_year = year > 0 ? year : year + 1;
    let is_leap;
    if (astronomical_year < 1582) is_leap = (astronomical_year % 4 === 0);
    else is_leap = (astronomical_year % 4 === 0 && astronomical_year % 100 !== 0)
      || (astronomical_year % 400 === 0);
    const days_in_months = [31, is_leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    const n_days = days_in_months.slice(0, month - 1).reduce((s, x) => s + x, 0) + day;

    const b_rad = 2 * Math.PI * (n_days - 81) / 364;
    const eot_offset = 9.87 * Math.sin(2 * b_rad) - 7.53 * Math.cos(b_rad) - 1.5 * Math.sin(b_rad);
    const total_delta = lng_offset + eot_offset;

    const approx_jd = date_to_julian_day(year, month, day, hour, minute) + (total_delta / 1440.0);
    const z = Math.floor(approx_jd + 0.5);
    let a;
    if (z < 2299161) a = z;
    else {
      const alpha = floordiv(z - 1867216.25, 36524.25);
      a = z + 1 + alpha - floordiv(alpha, 4);
    }
    const b = a + 1524;
    const c = floordiv(b - 122.1, 365.25);
    const d = Math.floor(365.25 * c);
    const e = floordiv(b - d, 30.6001);
    t_day = b - d - Math.floor(30.6001 * e);
    t_month = (e < 14) ? (e - 1) : (e - 13);
    t_year = (t_month > 2) ? (c - 4716) : (c - 4715);

    if (year < 0 && t_year <= 0) t_year -= 1;

    const total_mins = hour * 60 + minute + total_delta;
    t_hour = floordiv(pymod(total_mins, 1440), 60);
    t_min = Math.floor(pymod(total_mins, 60));
  }

  const jd = date_to_julian_day(t_year, t_month, t_day, t_hour, t_min);
  const day_ganzhi_idx = pymod(Math.floor(jd + 0.5 + 49), 60);
  const day_tg = TIANGAN[day_ganzhi_idx % 10];
  const day_dz = DIZHI[day_ganzhi_idx % 12];
  const y_idx = (t_year > 0) ? pymod(t_year - 4, 60) : pymod(t_year - 3, 60);
  const year_tg = TIANGAN[y_idx % 10], year_dz = DIZHI[y_idx % 12];
  const month_tg = TIANGAN[pymod(pymod(y_idx, 5) * 2 + t_month, 10)];
  const month_dz = DIZHI[pymod(t_month + 12, 12)];
  const shifted_minutes = pymod(t_hour * 60 + t_min + 60, 1440);
  const hour_dz_idx = floordiv(shifted_minutes, 120);
  const hour_dz = DIZHI[hour_dz_idx];
  const hour_tg = TIANGAN[pymod(pymod(TIANGAN.indexOf(day_tg), 5) * 2 + hour_dz_idx, 10)];
  const ri_zhu = day_tg;

  return {
    t_year, t_month, t_day, t_hour, t_min, jd,
    year_tg, year_dz, month_tg, month_dz, day_tg, day_dz, hour_tg, hour_dz,
    ri_zhu, original_year: year, longitude
  };
}

function generate_report(result) {
  const { ri_zhu, year_tg, year_dz, month_tg, month_dz, day_dz, hour_tg, hour_dz } = result;
  const me_x = WU_XING[ri_zhu];
  const month_relation = get_shishen_relation(ri_zhu, month_dz);

  const all_symbols = [year_tg, year_dz, month_tg, month_dz, ri_zhu, day_dz, hour_tg, hour_dz];
  const elements_count = { "木":0, "火":0, "土":0, "金":0, "水":0 };
  all_symbols.forEach(sym => { elements_count[WU_XING[sym]] += 1; });

  const elements_order = ["木","火","土","金","水"];
  const parent_element = elements_order[pymod(elements_order.indexOf(me_x) - 1, 5)];
  const self_power = elements_count[me_x] + elements_count[parent_element];
  const power_status = (self_power >= 4) ? "身强 / 能量充沛" : "身弱 / 需借力发展";

  const detail = PATTERN_DETAILS[month_relation] || FALLBACK_DETAIL;

  return { me_x, month_relation, elements_count, parent_element, self_power, power_status, detail };
}

/* 浏览器与 Node 双端导出 */
if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    is_valid_date, date_to_julian_day, get_shishen_relation,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL
  };
} else {
  window.BaziEngine = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    is_valid_date, date_to_julian_day, get_shishen_relation,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL
  };
}