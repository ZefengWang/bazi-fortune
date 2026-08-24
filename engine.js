"use strict";

/* =====================================================================
 * 八字命理排盘引擎（全球全历史·高精度演示版）
 * 仅供学习研究使用，严禁商用。
 * 关键能力：
 *   1) 时区→UTC 自动换算（IANA 时区，浏览器 Intl 原生处理夏令时）
 *   2) 节气（立春换年 / 以节定月）—— VSOP 近似算法，精度秒级
 *   3) 真太阳时纠正（经度 + 均时差）
 *   4) 地支藏干 + 加权身强弱判断 + 喜用神方向
 * 说明：排盘基准统一为「绝对 UTC 儒略日」，时区仅影响本地钟表读数。
 * =====================================================================
 */

/* ---------------- 0. 通用算子 ---------------- */
const floordiv = (a, b) => Math.floor(a / b);          // Python // 语义
const pymod = (a, n) => ((a % n) + n) % n;             // Python % 语义（恒非负）
const norm360 = d => ((d % 360) + 360) % 360;          // 角度归一化 [0,360)
const normDelta = d => { d = norm360(d); return d > 180 ? d - 360 : d; }; // 归一到 [-180,180]

/* ---------------- 1. 符号集与属性矩阵 ---------------- */
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

/* 地支藏干（主气 / 中气 / 余气） */
const HIDDEN_STEMS = {
  "子":["癸"],
  "丑":["己","癸","辛"],
  "寅":["甲","丙","戊"],
  "卯":["乙"],
  "辰":["戊","乙","癸"],
  "巳":["丙","庚","戊"],
  "午":["丁","己"],
  "未":["己","丁","乙"],
  "申":["庚","壬","戊"],
  "酉":["辛"],
  "戌":["戊","辛","丁"],
  "亥":["壬","甲"]
};
/* 藏干力量权重（本气/中气/余气，单藏干记 100） */
const HIDDEN_WEIGHT = [100, 60, 30];

/* 中国省级经度回退表（已由 cities-data.js 取代，此处保留兜底） */
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

/* ---------------- 2. 历法与天文学 ---------------- */
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

/* 公历（格列历）→ 儒略日（含时分小数） */
function date_to_julian_day(year, month, day, hour = 0, minute = 0) {
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

/* ΔT = TT - UT（秒），用于把力学时转成世界时。NASA 多项式分段表。 */
function deltaT(year) {
  const T = [
    [-4000,108371.7,-13036.80,392.000,0.0000],[-500,17201.0,-627.82,16.170,-0.3413],
    [-150,12200.6,-346.41,5.403,-0.1593],[150,9113.8,-328.13,-1.647,0.0377],
    [500,5707.5,-391.41,0.915,0.3145],[900,2203.4,-283.45,13.034,-0.1778],
    [1300,490.1,-57.35,2.085,-0.0072],[1600,120.0,-9.81,-1.532,0.1403],
    [1700,10.2,-0.91,0.510,-0.0370],[1800,13.4,-0.72,0.202,-0.0193],
    [1830,7.8,-1.81,0.416,-0.0247],[1860,8.3,-0.13,-0.406,0.0292],
    [1880,-5.4,0.32,-0.183,0.0173],[1900,-2.3,2.06,0.169,-0.0135],
    [1920,21.2,1.69,-0.304,0.0167],[1940,24.2,1.22,-0.064,0.0031],
    [1960,33.2,0.51,0.231,-0.0109],[1980,51.0,1.29,-0.026,0.0032],
    [2000,63.87,0.1,0,0]
  ];
  let i = 0;
  for (let k = 0; k < T.length; k++) if (year >= T[k][0]) i = k;
  if (i === T.length - 1) { // 2000 年后外推
    const y = year;
    if (y <= 2014) return 64.7 + (y - 2005) * 0.4;
    const f = yy => -20 + 31 * Math.pow((yy - 1820) / 100, 2);
    const F2014 = 64.7 + (2014 - 2005) * 0.4;
    if (y >= 2114) return f(y);
    return f(y) - (2114 - y) * (f(2014) - F2014) / 100;
  }
  const [Y1, a, b, c, d] = T[i], Y2 = T[i + 1][0];
  const t1 = (year - Y1) / (Y2 - Y1) * 10, t2 = t1 * t1, t3 = t2 * t1;
  return a + b * t1 + c * t2 + d * t3;
}

/* 太阳视黄经（度，几何平黄经 + VSOP 主要摄动项）。t 为 TT 儒略世纪。 */
function solarLongitudeDeg(t) {
  const t2 = t * t, t3 = t2 * t, t4 = t3 * t;
  let L = 48950621.66 + 6283319653.318 * t + 52.9674 * t2 + 0.00432 * t3 - 0.001124 * t4
    + 334166 * Math.cos(4.669257 + 628.307585 * t)
    + 3489 * Math.cos(4.6261 + 1256.61517 * t)
    + 350 * Math.cos(2.744 + 575.3385 * t)
    + 342 * Math.cos(2.829 + 0.3523 * t)
    + 314 * Math.cos(3.628 + 7771.3771 * t)
    + 268 * Math.cos(4.418 + 786.0419 * t)
    + 234 * Math.cos(6.135 + 393.021 * t)
    + 132 * Math.cos(0.742 + 1150.677 * t)
    + 127 * Math.cos(2.037 + 52.9691 * t)
    + 120 * Math.cos(1.11 + 157.7344 * t)
    + 99 * Math.cos(5.23 + 588.493 * t)
    + 90 * Math.cos(2.05 + 2.63 * t)
    + 86 * Math.cos(3.51 + 39.815 * t)
    + 78 * Math.cos(1.18 + 522.369 * t)
    + 75 * Math.cos(2.53 + 550.755 * t)
    + 51 * Math.cos(4.58 + 1884.923 * t)
    + 49 * Math.cos(4.21 + 77.552 * t)
    + 36 * Math.cos(2.92 + 0.07 * t)
    + 32 * Math.cos(5.85 + 1179.063 * t)
    + 28 * Math.cos(1.9 + 79.63 * t)
    + 27 * Math.cos(0.31 + 1097.71 * t)
    + 2060.6 * Math.cos(2.67823 + 628.307585 * t) * t
    + 43.0 * Math.cos(2.635 + 1256.6152 * t) * t
    + 8.72 * Math.cos(1.072 + 628.3076 * t) * t2
    - 994 - 834 * Math.sin(2.1824 - 33.75705 * t)
    - 64 * Math.sin(3.5069 + 1256.66393 * t);
  return norm360((L / 10000000) * 180 / Math.PI);
}

// 24 节气近似日期（公历月/日），用于二分初值
const APPROX = [[2,4],[2,19],[3,6],[3,21],[4,5],[4,20],[5,6],[5,21],[6,6],[6,21],[7,7],[7,23],[8,8],[8,23],[9,8],[9,23],[10,8],[10,23],[11,7],[11,22],[12,7],[12,22],[1,6],[1,20]];
const TERM_NAMES = ["立春","雨水","惊蛰","春分","清明","谷雨","立夏","小满","芒种","夏至","小暑","大暑","立秋","处暑","白露","秋分","寒露","霜降","立冬","小雪","大雪","冬至","小寒","大寒"];

/**
 * 求某年第 i 个节气（i: 0=立春 …… 23=大寒）发生的绝对 UT 儒略日。
 * 二分法解太阳视黄经 = 315 + 15·i 的时刻，精度秒级。
 */
function solarTermUtJd(year, i) {
  const W = norm360(315 + 15 * i);
  const [mo, dy] = APPROX[i];
  const tApp = (date_to_julian_day(year, mo, dy) - 2451545) / 36525;
  let lo = tApp - 0.0001, hi = tApp + 0.0001;   // ±3.65 天
  let flo = normDelta(solarLongitudeDeg(lo) - W);
  let fhi = normDelta(solarLongitudeDeg(hi) - W);
  if (flo > fhi) { [lo, hi] = [hi, lo]; [flo, fhi] = [fhi, flo]; }
  for (let k = 0; k < 60; k++) {
    const mid = (lo + hi) / 2;
    if (normDelta(solarLongitudeDeg(mid) - W) >= 0) hi = mid; else lo = mid;
  }
  const t = (lo + hi) / 2;
  const dt = deltaT(year);
  return 2451545 + t * 36525 - dt / 86400;      // 绝对 UT 儒略日
}

/* 均时差（分钟）：真太阳时 = 平太阳时 + EoT。近似公式，误差 < 30 秒。 */
function equationOfTime(year, month, day) {
  const astro_year = year > 0 ? year : year + 1;
  let is_leap;
  if (astro_year < 1582) is_leap = (astro_year % 4 === 0);
  else is_leap = (astro_year % 4 === 0 && astro_year % 100 !== 0) || (astro_year % 400 === 0);
  const dim = [31, is_leap ? 29 : 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
  const n_days = dim.slice(0, month - 1).reduce((s, x) => s + x, 0) + day;
  const b_rad = 2 * Math.PI * (n_days - 81) / 364;
  return 9.87 * Math.sin(2 * b_rad) - 7.53 * Math.cos(b_rad) - 1.5 * Math.sin(b_rad);
}

/* ---------------- 3. 时区 ---------------- */
const _dtfCache = Object.create(null);

/* 获取某 UTC 时刻（毫秒）在指定 IANA 时区的偏移量（毫秒，东正西负） */
function getTimeZoneOffsetMs(ts, timeZone) {
  let dtf = _dtfCache[timeZone];
  if (!dtf) {
    try {
      dtf = new Intl.DateTimeFormat("en-US", {
        timeZone,
        year: "numeric", month: "2-digit", day: "2-digit",
        hour: "2-digit", minute: "2-digit", second: "2-digit", hourCycle: "h23"
      });
    } catch (e) {
      throw new Error("无效的时区标识：" + timeZone);
    }
    _dtfCache[timeZone] = dtf;
  }
  const parts = {};
  for (const p of dtf.formatToParts(ts)) parts[p.type] = p.value;
  const y = +parts.year, mo = +parts.month, d = +parts.day;
  const h = +parts.hour, mi = +parts.minute, s = +parts.second;
  const asUTC = Date.UTC(y, mo - 1, d, h, mi, s);
  return asUTC - ts;
}

/* 稳妥构造"年份 y-mo-d h:mi:s"对应的 UTC 毫秒（处理 0-99 年 Date.UTC 怪癖） */
function dateToMsUtc(y, mo, d, h, mi) {
  let ms = Date.UTC(y, mo - 1, d, h, mi, 0);
  if (y >= 0 && y <= 99) {
    const dt = new Date(ms);
    dt.setUTCFullYear(y);
    ms = dt.getTime();
  }
  return ms;
}

/* 当地钟表时间 → UTC 毫秒。固定点迭代收敛夏令时边界（折叠歧义 1 小时除外）。 */
function localToUtcMs(y, mo, d, h, mi, timeZone) {
  const localMs = dateToMsUtc(y, mo, d, h, mi);
  let ts = localMs;
  for (let i = 0; i < 2; i++) {
    ts = localMs - getTimeZoneOffsetMs(ts, timeZone);
  }
  return ts;
}

/* 获取该时区"标准时间（非夏令时）"的固定偏移（分钟，东正西负）。
 * 原理：对同一年取 12 个代表日（每月 15 日）求偏移，取其中的"最小值"
 * （夏令时总是让偏移增大 60 分钟，故全年偏移最小值即标准时间基准偏移），
 * 避免被出生日期是否处于 DST 影响。
 * 用于"输入时间为标准时间、不自动套夏令时"的用户选项（默认）。 */
function getStandardOffsetMin(timeZone) {
  let min = Infinity;
  for (let mo = 1; mo <= 12; mo++) {
    const y = 2024, d = 15, h = 12, mi = 0;
    const lms = dateToMsUtc(y, mo, d, h, mi);
    let ts = lms;
    for (let i = 0; i < 2; i++) ts = lms - getTimeZoneOffsetMs(ts, timeZone);
    const off = Math.round((lms - ts) / 60000);
    if (off < min) min = off;
  }
  return min;
}

const msToJd = ms => ms / 86400000 + 2440587.5;

/* ---------------- 4. 格局详解数据 ---------------- */
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

/* ---------------- 5. 十神 ---------------- */
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

/* 地支本气（主气）天干 —— 用于月令格局判定，避免地支阴阳 ≠ 主气干阴阳的偏差 */
function primaryHiddenStem(branch) {
  return HIDDEN_STEMS[branch][0];
}

/* ---------------- 6. 核心排盘 ---------------- */
/**
 * 全球排盘主入口
 * @param number year/month/day/hour/minute  出生地当地钟表时间
 * @param number longitude  出生地经度（东经正、西经负）
 * @param string timezone   IANA 时区（如 "Asia/Shanghai"、"America/New_York"）
 * @param number time_type  1=现代行政时间（自动转真太阳时）；2=古代视太阳时（输入已校准）
 */
function execute_global_fortune_engine(year, month, day, hour, minute, longitude, timezone, time_type, use_dst) {
  let t_year = year, t_month = month, t_day = day, t_hour = hour, t_min = minute;
  let offset_min = 0, eot_min = 0;

  if (time_type === 1) {
    // 1) 时区偏移（分钟，东正西负）。
    const inputMs = dateToMsUtc(year, month, day, hour, minute);
    // use_dst: true=用户声明所填时间为夏令时（按当日真实偏移）；false/未传=标准时间（去掉夏令时）
    const utcMs = use_dst
      ? localToUtcMs(year, month, day, hour, minute, timezone)
      : dateToMsUtc(year, month, day, hour, minute) - getStandardOffsetMin(timezone) * 60000;
    offset_min = Math.round((inputMs - utcMs) / 60000);

    // 2) 均时差
    eot_min = equationOfTime(year, month, day);

    // 3) 真太阳时修正总量：total_delta = (经度×4 + 均时差) - 时区偏移
    //    对国内(offset=480)退化为 (经度-120)×4 + 均时差，与旧算法完全一致。
    const total_delta = (longitude * 4 + eot_min) - offset_min;

    // 4) 由修正后的绝度儒略日反解出"真太阳时读数"的日历（跨日自动进位/退位）
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

  // 绝对 UTC 儒略日 = 输入日历（当地）JD - 时区偏移 / 天
  const utc_jd = date_to_julian_day(year, month, day, hour, minute) - (time_type === 1 ? offset_min / 1440.0 : 0);
  // 真太阳时对应的绝对儒略日（用于节气比较与日柱）
  const solar_ut_jd = utc_jd + ((time_type === 1 ? (longitude * 4 + eot_min) : 0)) / 1440.0;

  // 日柱：以真太阳时刻换日（子时归次日的争议此处沿用"午夜换日"口径，与旧版一致）
  const jd = date_to_julian_day(t_year, t_month, t_day, t_hour, t_min);
  const day_ganzhi_idx = pymod(Math.floor(jd + 0.5 + 49), 60);
  const day_tg = TIANGAN[day_ganzhi_idx % 10];
  const day_dz = DIZHI[day_ganzhi_idx % 12];

  // —— 年柱：立春换年（节气为绝对时刻，须与出生绝对 UTC 时刻比较）——
  const cal_year = t_year;
  const li_chun_this = solarTermUtJd(cal_year, 0);
  const bz_year = (utc_jd < li_chun_this) ? (cal_year - 1) : cal_year;
  const y_idx = (bz_year > 0) ? pymod(bz_year - 4, 60) : pymod(bz_year - 3, 60);
  const year_tg = TIANGAN[y_idx % 10], year_dz = DIZHI[y_idx % 12];

  // —— 月柱：以节定月（寅月=立春起，丑月止于次年立春）——
  const year_gan_idx = pymod(bz_year > 0 ? bz_year - 4 : bz_year - 3, 10);
  const base = pymod(year_gan_idx * 2 + 2, 10);   // 五虎遁首月天干
  const starts = [];
  for (let k = 0; k < 11; k++) starts.push(solarTermUtJd(bz_year, 2 * k)); // 立春..大雪
  starts.push(solarTermUtJd(bz_year + 1, 22));                              // 小寒(次年)
  let month_idx = 0;
  for (let k = 1; k < 12; k++) {
    if (utc_jd >= starts[k]) month_idx = k; else break;
  }
  const month_tg = TIANGAN[pymod(base + month_idx, 10)];
  const month_dz = DIZHI[pymod(2 + month_idx, 12)];

  // —— 时柱（真太阳时读数，23:00 起为早子时归次日）——
  const shifted_minutes = pymod(t_hour * 60 + t_min + 60, 1440);
  const hour_dz_idx = floordiv(shifted_minutes, 120);
  const hour_dz = DIZHI[hour_dz_idx];
  const hour_tg = TIANGAN[pymod(pymod(TIANGAN.indexOf(day_tg), 5) * 2 + hour_dz_idx, 10)];

  const ri_zhu = day_tg;

  return {
    t_year, t_month, t_day, t_hour, t_min, jd, utc_jd, solar_ut_jd,
    year_tg, year_dz, month_tg, month_dz, day_tg, day_dz, hour_tg, hour_dz,
    ri_zhu, original_year: year, longitude, timezone,
    offset_min, eot_min, bz_year
  };
}

/* ---------------- 7. 解译报告（含藏干、身强弱、喜用神） ---------------- */
const ELEMENT_ORDER = ["木","火","土","金","水"];

/* —— 8. 大运 / 流年 ——
 * 起运岁数与排运方向：
 *   ctxgender: 'male'|'female'
 *   年干阳 → 男顺女逆；年干阴 → 男逆女顺。
 *   起运：顺排取出生时刻之后最近一个"节"，逆排取之前最近一个"节"，
 *        间隔天数 ÷3 折算起运年（1 天 = 4 个月）。
 *   "节"取节气序号中的双数索引（0 立春、2 惊蛰、4 清明 …… 22 小寒）。
 */

/* JD → 公历日期（格列历，格） */
function jdToDate(jd) {
  const z = Math.floor(jd + 0.5);
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
  const day = b - d - Math.floor(30.6001 * e);
  const month = (e < 14) ? e - 1 : e - 13;
  let year = (month > 2) ? c - 4716 : c - 4715;
  if (year <= 0) year -= 1;
  return { year, month, day };
}

/* 附近 5 年内较大范围的"节"查找 */
function nearestSolarTermJd(birth_jd, dir, bz_year) {
  // dir: 1 → 找出生点之后最近的节；-1 → 之前最近的节
  // 覆盖出生年前后若干年，保证能找到
  for (let yr = bz_year - 2; yr <= bz_year + 2; yr++) {
    for (let i = 0; i < 24; i += 2) {          // 只取"节"（索引 0,2,4,...22）
      const term = solarTermUtJd(yr, i);
      const gap = term - birth_jd;
      if (dir === 1 && gap > 1e-4) return term;
      if (dir === -1 && gap < -1e-4) return term;
    }
  }
  return null;
}

function computeDayunAndLiuNian(result, bz_report, gender) {
  const { year_tg, month_tg, month_dz, bz_year, utc_jd } = result;
  const year_gan_yang = YIN_YANG[year_tg] === "阳";   // 年干阴阳
  const is_male = gender === "male";
  // 阳年男 / 阴年女 → 顺排；阴年男 / 阳年女 → 逆排
  const forward = (year_gan_yang === is_male);

  const start = nearestSolarTermJd(utc_jd, forward ? 1 : -1, bz_year);
  let qi_yun_age = 0, qi_yun_days = 0, qi_yun_year = bz_year, qi_yun_date = "";
  if (start != null) {
    // 出生在节之后到下一个节之间的天数 / 前一个节到出生之间的天数
    let span;
    if (forward) span = start - utc_jd;
    else {
      const prev = nearestSolarTermJd(utc_jd, -1, bz_year);
      span = prev != null ? utc_jd - prev : 0;
    }
    qi_yun_days = span;
    // 3 天 = 1 年；余数 1 天 = 4 个月；1/6 天 ≈ 1 年（以小时计）
    const total_days = span;
    qi_yun_age = total_days / 3.0;
    qi_yun_year = bz_year + Math.floor(qi_yun_age);
    // 精确起运公历日期（无闰余近似）
    const qiJd = utc_jd + span * (forward ? 1 : 1);
    const d = jdToDate(forward ? start : (nearestSolarTermJd(utc_jd, -1, bz_year) || start));
    qi_yun_date = `${d.year}-${String(d.month).padStart(2,"0")}-${String(d.day).padStart(2,"0")}`;
  }

  // 从月柱起排大运：顺排 → +1 推进；逆排 → -1
  const idx_tg = TIANGAN.indexOf(month_tg);
  const idx_dz = DIZHI.indexOf(month_dz);
  const step = forward ? 1 : -1;
  const dayun = [];
  let startAge = Math.floor(qi_yun_age < 0 ? 0 : qi_yun_age);
  for (let k = 0; k < 8; k++) {
    const tg = TIANGAN[pymod(idx_tg + step * (k + 1), 10)];
    const dz = DIZHI[pymod(idx_dz + step * (k + 1), 12)];
    const from = startAge + k * 10;
    const to = from + 9;
    const ss = get_shishen_relation(result.ri_zhu, tg);
    dayun.push({ gan: tg, zhi: dz, from, to, shishen: ss });
  }

  return { qi_yun_age, qi_yun_days, qi_yun_date, dayun, forward };
}

/* 流年干支：以立春换年（与年柱口径一致） */
function liunianGanzhi(birth_info, year) {
  const ly = birth_info && birth_info.bz_year !== undefined ? year : year;
  const li_chun = solarTermUtJd(year, 0);
  const bz = birth_info && birth_info.utc_jd !== undefined && birth_info.utc_jd < li_chun
    ? year - 1 : year;
  const y_idx = (bz > 0) ? pymod(bz - 4, 60) : pymod(bz - 3, 60);
  return { gan: TIANGAN[y_idx % 10], zhi: DIZHI[y_idx % 12], year, bz };
}

/* 生我者（印的五行） */
function parentElementOf(me_x) {
  return ELEMENT_ORDER[pymod(ELEMENT_ORDER.indexOf(me_x) - 1, 5)];
}

/* 加权身强弱评分 */
function evaluateStrength(ri_zhu, stems, branches, month_dz) {
  const me_x = WU_XING[ri_zhu];
  const parent_x = parentElementOf(me_x);
  const is_ally = wx => (wx === me_x || wx === parent_x);

  const power = { "木":0, "火":0, "土":0, "金":0, "水":0 };
  let ally = 0, foe = 0;

  // 天干：每个记 100
  for (const s of stems) {
    const w = 100;
    power[WU_XING[s]] += w;
    if (is_ally(WU_XING[s])) ally += w; else foe += w;
  }
  // 地支：藏干按本/中/余气加权，月令(月支)整体 ×1.6（得令）
  branches.forEach((bz, i) => {
    const hidden = HIDDEN_STEMS[bz];
    const mf = (bz === month_dz) ? 1.6 : 1.0;
    hidden.forEach((stem, k) => {
      const w = (hidden.length === 1) ? 100 : (HIDDEN_WEIGHT[k] || 0);
      const v = w * mf;
      power[WU_XING[stem]] += v;
      if (is_ally(WU_XING[stem])) ally += v; else foe += v;
    });
  });

  const total = ally + foe;
  const ratio = total > 0 ? ally / total : 0.5;
  let label;
  if (ratio >= 0.62) label = "身强 · 能量充盈";
  else if (ratio >= 0.55) label = "身偏强";
  else if (ratio <= 0.38) label = "身弱 · 需借力发展";
  else if (ratio <= 0.45) label = "身偏弱";
  else label = "中和";

  // 喜用神方向
  let yong;
  if (ratio >= 0.55) yong = "克泄耗（官杀 / 食伤 / 财）";
  else if (ratio <= 0.45) yong = "生扶（正偏印 / 比劫）";
  else yong = "五行流通（顺势而为）";

  return { power, ally, foe, ratio, label, yong };
}

function generate_report(result) {
  const { ri_zhu, year_tg, year_dz, month_tg, month_dz, day_dz, hour_tg, hour_dz } = result;
  const me_x = WU_XING[ri_zhu];

  // 月令格局：以月支本气天干论十神
  const month_primary = primaryHiddenStem(month_dz);
  const month_relation = get_shishen_relation(ri_zhu, month_primary);

  const all_symbols = [year_tg, year_dz, month_tg, month_dz, ri_zhu, day_dz, hour_tg, hour_dz];
  const elements_count = { "木":0, "火":0, "土":0, "金":0, "水":0 };
  all_symbols.forEach(sym => { elements_count[WU_XING[sym]] += 1; });

  const stems = [year_tg, month_tg, ri_zhu, hour_tg];
  const branches = [year_dz, month_dz, day_dz, hour_dz];
  const strength = evaluateStrength(ri_zhu, stems, branches, month_dz);

  // 藏干明细（供前端展示）
  const hidden_stems = {
    "年": { "支": year_dz, "藏干": HIDDEN_STEMS[year_dz] },
    "月": { "支": month_dz, "藏干": HIDDEN_STEMS[month_dz] },
    "日": { "支": day_dz, "藏干": HIDDEN_STEMS[day_dz] },
    "时": { "支": hour_dz, "藏干": HIDDEN_STEMS[hour_dz] }
  };

  // 十神总览（相对日主）
  const shishen = {
    "年干": get_shishen_relation(ri_zhu, year_tg),
    "月干": get_shishen_relation(ri_zhu, month_tg),
    "日主": "元男/元女",
    "时干": get_shishen_relation(ri_zhu, hour_tg),
    "月令": month_relation
  };

  const detail = PATTERN_DETAILS[month_relation] || FALLBACK_DETAIL;
  const parent_element = parentElementOf(me_x);

  return {
    me_x, month_relation, elements_count, elements_power: strength.power,
    parent_element, strength, hidden_stems, shishen,
    power_status: strength.label, yong_shen: strength.yong,
    detail
  };
}

/* ---------------- 导出（浏览器 / Node 双端） ---------------- */
if (typeof module !== "undefined" && module.exports) {
  module.exports = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    HIDDEN_STEMS, TERM_NAMES,
    is_valid_date, date_to_julian_day, get_shishen_relation, primaryHiddenStem,
    solarTermUtJd, equationOfTime, localToUtcMs, getTimeZoneOffsetMs, getStandardOffsetMin,
    computeDayunAndLiuNian, liunianGanzhi, jdToDate,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL
  };
} else {
  window.BaziEngine = {
    TIANGAN, DIZHI, WU_XING, YIN_YANG, SHISHEN_MAP, PROVINCE_FALLBACK_LNG,
    HIDDEN_STEMS, TERM_NAMES,
    is_valid_date, date_to_julian_day, get_shishen_relation, primaryHiddenStem,
    solarTermUtJd, equationOfTime, localToUtcMs, getTimeZoneOffsetMs, getStandardOffsetMin,
    computeDayunAndLiuNian, liunianGanzhi, jdToDate,
    execute_global_fortune_engine, generate_report, PATTERN_DETAILS, FALLBACK_DETAIL
  };
}